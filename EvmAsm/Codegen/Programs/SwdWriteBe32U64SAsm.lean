/-
  EvmAsm.Codegen.Programs.SwdWriteBe32U64SAsm

  Verified SAsm port of `swd_write_be32_u64` (bead evm-asm-4ch8f.12.7): write
  the u64 in `a0` big-endian into the LOW 8 bytes of a zeroed 32-byte buffer
  at `a1` — i.e. the 32-byte big-endian storage-slot key of `a0`.

  Source (`swdWriteBe32U64_prog` in SystemWrites.lean, 21 instrs incl. ret):
  two sequential loops over the writable 32-byte slot at `a1`:
    * LOOP 1 (zero-fill): dst[0..32) := 0.
    * LOOP 2 (be write):  dst[24 + i] := (a0 >>> (56 - 8*i)) &&& 0xff  for
      i in 0..8 — the big-endian bytes of `a0` into the low 8 bytes.

  Net: `dst = replicate 24 0 ++ beBytes a0`.  Modelled over a single WRITABLE
  region `⟨a1, 32⟩` (no read-only region; loop-1 stores the hardwired `x0`,
  loop-2's value comes from register `a0`).

  The emitted routine is re-emitted from these verified structured loops. Each
  back-`JAL` now targets its guard rather than redundantly re-running the limit
  initialization. Exact flatten identity is kernel-pinned below. This changes
  two JAL immediates, so EEST A/B is required.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.SystemWrites

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SwdWriteBe32U64SAsm

/-- The `k`-th big-endian byte of `v`. -/
def beByte (v : Word) (k : Nat) : BitVec 8 :=
  BitVec.truncate 8 ((v >>> (56 - 8 * k)) &&& 255)

/-- The 8-byte big-endian encoding of `v`. -/
def beBytes (v : Word) : List (BitVec 8) :=
  (List.range 8).map (beByte v)

#guard beBytes 0x0102030405060708 = [1, 2, 3, 4, 5, 6, 7, 8]

-- ============================================================================
-- Loop-1 window: zero-fill prefix
-- ============================================================================

/-- After `i` zero-fill iterations: the first `i` bytes are zero, the rest is
    the untouched original buffer. -/
def zeroWin (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate i (0 : BitVec 8) ++ orig.drop i

theorem zeroWin_zero (orig : List (BitVec 8)) : zeroWin orig 0 = orig := by
  simp [zeroWin]

theorem zeroWin_32_eq (orig : List (BitVec 8)) (h : orig.length = 32) :
    zeroWin orig 32 = List.replicate 32 (0 : BitVec 8) := by
  simp only [zeroWin, List.drop_eq_nil_of_le (by omega : orig.length ≤ 32),
    List.append_nil]

theorem length_zeroWin (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 32) (hi : i ≤ 32) : (zeroWin orig i).length = 32 := by
  simp only [zeroWin, List.length_append, List.length_replicate, List.length_drop, h]
  omega

theorem zeroWin_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 32) (hi : i < 32) :
    setBytes (zeroWin orig i) i [(0 : BitVec 8)] = zeroWin orig (i + 1) := by
  rw [setBytes_singleton]
  have hpre : (List.replicate i (0 : BitVec 8)).length = i := by simp
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [zeroWin, List.replicate_succ']
  rw [hdrop]
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self, List.set_cons_zero,
    List.append_assoc, List.singleton_append]

-- ============================================================================
-- Loop-2 window: big-endian bytes into the low 8 of a zero buffer
-- ============================================================================

/-- After `i` big-endian iterations, starting from an all-zero 32-byte buffer:
    24 zero bytes, then the first `i` big-endian bytes of `v`, then `8 - i`
    trailing zeros. -/
def beWin32 (v : Word) (i : Nat) : List (BitVec 8) :=
  List.replicate 24 (0 : BitVec 8)
    ++ (List.range i).map (beByte v)
    ++ List.replicate (8 - i) (0 : BitVec 8)

theorem beWin32_zero (v : Word) :
    beWin32 v 0 = List.replicate 32 (0 : BitVec 8) := by
  simp only [beWin32, List.range_zero, List.map_nil, List.append_nil, Nat.sub_zero]
  rw [List.replicate_append_replicate]

theorem beWin32_8_eq (v : Word) :
    beWin32 v 8 = List.replicate 24 (0 : BitVec 8) ++ beBytes v := by
  simp [beWin32, beBytes]

theorem length_beWin32 (v : Word) (i : Nat) (hi : i ≤ 8) :
    (beWin32 v i).length = 32 := by
  simp only [beWin32, List.length_append, List.length_replicate, List.length_map,
    List.length_range]
  omega

theorem beWin32_step (v : Word) (i : Nat) (hi : i < 8) :
    setBytes (beWin32 v i) (24 + i) [beByte v i] = beWin32 v (i + 1) := by
  rw [setBytes_singleton]
  have hpre : (List.replicate 24 (0 : BitVec 8) ++ (List.range i).map (beByte v)).length
      = 24 + i := by
    simp only [List.length_append, List.length_replicate, List.length_map, List.length_range]
  have htail : List.replicate (8 - i) (0 : BitVec 8)
      = (0 : BitVec 8) :: List.replicate (8 - (i + 1)) (0 : BitVec 8) := by
    rw [show 8 - i = (8 - (i + 1)) + 1 from by omega, List.replicate_succ]
  simp only [beWin32, htail, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    hpre, List.set_append_right, Nat.le_refl, Nat.sub_self, List.set_cons_zero]
  simp [List.append_assoc]

-- ============================================================================
-- Body
-- ============================================================================

def initBlock (limit : Word) : List Instr := [.LI .x5 0, .LI .x6 limit]

def zeroStepBlock : List Instr :=
  [.ADD .x7 .x11 .x5, .SB .x7 .x0 0, .ADDI .x5 .x5 1]

def beStepBlock : List Instr :=
  [.LI .x7 56, .SLLI .x28 .x5 3, .SUB .x7 .x7 .x28, .SRL .x29 .x10 .x7,
   .ANDI .x29 .x29 255, .ADDI .x30 .x11 24, .ADD .x30 .x30 .x5,
   .SB .x30 .x29 0, .ADDI .x5 .x5 1]

def zeroInv (v dst : Word) (orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = v ∧ rf.get .x11 = dst ∧ rf.get .x6 = 32 ∧
    rf.get .x5 = BitVec.ofNat 64 i ∧
    i ≤ 32 ∧ orig.length = 32 ∧ ws = zeroWin orig i

def beInv (v dst : Word) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = v ∧ rf.get .x11 = dst ∧ rf.get .x6 = 8 ∧
    rf.get .x5 = BitVec.ofNat 64 i ∧ i ≤ 8 ∧ ws = beWin32 v i

def swdWriteBe32U64Body (v dst : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init1" (initBlock 32) ;;;
  .«while» "loop1" (.bne .x5 .x6) 32 (zeroInv v dst orig)
    (.block "zero" zeroStepBlock) ;;;
  .block "init2" (initBlock 8) ;;;
  .«while» "loop2" (.bne .x5 .x6) 8 (beInv v dst)
    (.block "be" beStepBlock)

def swdWriteBe32U64Fn (v dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "swdWriteBe32U64"
  rw := ⟨dst, 32⟩
  pre := fun rf ws _ =>
    rf.get .x10 = v ∧ rf.get .x11 = dst ∧ ws = orig ∧ orig.length = 32
  post := fun _ ws _ => ws = List.replicate 24 (0 : BitVec 8) ++ beBytes v
  body := swdWriteBe32U64Body v dst orig

def swdWriteBe32U64_verified : Program :=
  (swdWriteBe32U64Body 0 0 []).flatten 0

#guard (swdWriteBe32U64_verified : List Instr).length = 20
#guard (swdWriteBe32U64Body 0 0 []).flatten 0
  = (swdWriteBe32U64Body 0 0 []).flatten 0x80000000

-- Emitted instructions, pinned exactly. Both verified structured-loop
-- back-edges target their guards (`-16` and `-40`).
#guard (swdWriteBe32U64Body 0 0 []).flatten 0 =
  [.LI .x5 0, .LI .x6 32,
   .BEQ .x5 .x6 (20 : BitVec 13),
   .ADD .x7 .x11 .x5, .SB .x7 .x0 0, .ADDI .x5 .x5 1, .JAL .x0 (-16 : BitVec 21),
   .LI .x5 0, .LI .x6 8,
   .BEQ .x5 .x6 (44 : BitVec 13),
   .LI .x7 56, .SLLI .x28 .x5 3, .SUB .x7 .x7 .x28, .SRL .x29 .x10 .x7,
   .ANDI .x29 .x29 255, .ADDI .x30 .x11 24, .ADD .x30 .x30 .x5,
   .SB .x30 .x29 0, .ADDI .x5 .x5 1, .JAL .x0 (-40 : BitVec 21)]
#guard (swdWriteBe32U64Body 0 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] =
  swdWriteBe32U64_prog

-- ============================================================================
-- Engines (own heartbeat budget)
-- ============================================================================

def zeroStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x7 (rf.get .x11 + rf.get .x5)
  r1.set .x5 (r1.get .x5 + signExtend12 (1 : BitVec 12))

theorem zeroStepRf_get_x10 (rf : RegFile) : (zeroStepRf rf).get .x10 = rf.get .x10 := by
  unfold zeroStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7)]

theorem zeroStepRf_get_x11 (rf : RegFile) : (zeroStepRf rf).get .x11 = rf.get .x11 := by
  unfold zeroStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7)]

theorem zeroStepRf_get_x6 (rf : RegFile) : (zeroStepRf rf).get .x6 = rf.get .x6 := by
  unfold zeroStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]

theorem zeroStepRf_get_x5 (rf : RegFile) :
    (zeroStepRf rf).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hx5 : rf.get .x5 = BitVec.ofNat 64 i) (hx11 : rf.get .x11 = dst) :
    execBlock reg dst rf ws zeroStepBlock
      = (zeroStepRf rf, setBytes ws i [(0 : BitVec 8)]) := by
  have haddr : (rf.get .x11 + rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [hx11, hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  · rfl
  · show setBytes ws ((rf.get .x11 + rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat)
        [BitVec.truncate 8 (rf.get .x0)] = setBytes ws i [(0 : BitVec 8)]
    rw [haddr, RegFile.get_x0]
    rfl

def beStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x7 (56 : Word)
  let r2 := r1.set .x28 (r1.get .x5 <<< (3 : BitVec 6).toNat)
  let r3 := r2.set .x7 (r2.get .x7 - r2.get .x28)
  let r4 := r3.set .x29 (r3.get .x10 >>> ((r3.get .x7).toNat % 64))
  let r5 := r4.set .x29 (r4.get .x29 &&& signExtend12 (255 : BitVec 12))
  let r6 := r5.set .x30 (r5.get .x11 + signExtend12 (24 : BitVec 12))
  let r7 := r6.set .x30 (r6.get .x30 + r6.get .x5)
  r7.set .x5 (r7.get .x5 + signExtend12 (1 : BitVec 12))

theorem beStepRf_get_x10 (rf : RegFile) : (beStepRf rf).get .x10 = rf.get .x10 := by
  unfold beStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28)]

theorem beStepRf_get_x11 (rf : RegFile) : (beStepRf rf).get .x11 = rf.get .x11 := by
  unfold beStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28)]

theorem beStepRf_get_x6 (rf : RegFile) : (beStepRf rf).get .x6 = rf.get .x6 := by
  unfold beStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]

theorem beStepRf_get_x5 (rf : RegFile) :
    (beStepRf rf).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold beStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem store_val_eq_beByte (v : Word) (i : Nat) (hi : i < 8) :
    BitVec.truncate 8
        ((v >>> ((56 - BitVec.ofNat 64 i <<< (3 : BitVec 6).toNat).toNat % 64))
          &&& signExtend12 (255 : BitVec 12))
      = beByte v i := by
  have hsh : (56 - BitVec.ofNat 64 i <<< (3 : BitVec 6).toNat : Word).toNat % 64
      = 56 - 8 * i := by
    interval_cases i <;> decide
  rw [hsh, show signExtend12 (255 : BitVec 12) = (255 : Word) from by decide]
  rfl

theorem be_engine (reg : Region) (dst v : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 8)
    (hx5 : rf.get .x5 = BitVec.ofNat 64 i) (hx10 : rf.get .x10 = v)
    (hx11 : rf.get .x11 = dst) :
    execBlock reg dst rf ws beStepBlock
      = (beStepRf rf, setBytes ws (24 + i) [beByte v i]) := by
  have haddr : (rf.get .x11 + signExtend12 (24 : BitVec 12) + rf.get .x5
      + signExtend12 (0 : BitVec 12) - dst).toNat = 24 + i := by
    rw [hx11, hx5, show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  · rfl
  · show setBytes ws ((rf.get .x11 + signExtend12 (24 : BitVec 12) + rf.get .x5
        + signExtend12 (0 : BitVec 12) - dst).toNat)
        [BitVec.truncate 8 ((rf.get .x10 >>>
            ((56 - rf.get .x5 <<< (3 : BitVec 6).toNat).toNat % 64)) &&& signExtend12 255)]
      = setBytes ws (24 + i) [beByte v i]
    rw [haddr, hx10, hx5, store_val_eq_beByte v i hi]

-- ============================================================================
-- Spec
-- ============================================================================

theorem swdWriteBe32U64Fn_spec (v dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 32⟩) (base : Word) :
    (swdWriteBe32U64Fn v dst orig).Spec base := by
  have hbase : (swdWriteBe32U64Fn v dst orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case swdWriteBe32U64.loop1.inv_init =>
    rintro rf' ws' A' ⟨rf₀, ws₀, -, ⟨hx10, hx11, hws0, hlen⟩, rfl, rfl⟩
    simp only [initBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem, zeroInv]
    refine ⟨?_, ?_, ?_, ?_, by omega, hlen, hws0.trans (zeroWin_zero orig).symm⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]; exact hx10
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]; exact hx11
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]; rfl
  case swdWriteBe32U64.loop1.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx11, hx6, hx5, -, hlen, hws0⟩, -⟩, rfl, rfl⟩
    simp only [hbase]
    rw [zero_engine _ dst rf₀ ws₀ i hi hx5 hx11]
    refine ⟨?_, ?_, ?_, ?_, by omega, hlen, ?_⟩
    · rw [zeroStepRf_get_x10]; exact hx10
    · rw [zeroStepRf_get_x11]; exact hx11
    · rw [zeroStepRf_get_x6]; exact hx6
    · rw [zeroStepRf_get_x5, hx5, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from by decide]
      omega
    · rw [hws0, zeroWin_step orig i hlen hi]
  case swdWriteBe32U64.loop1.exhausted =>
    rintro rf ws A ⟨-, -, hx6, hx5, -, -, -⟩
    simp only [Cond.holds, hx5, hx6, not_not]
    decide
  case swdWriteBe32U64.loop1.body.zero.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨-, hx11, hx6, hx5, -, -, -⟩, -⟩
    have haddr : (rf.get .x11 + rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
      rw [hx11, hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hwslen : ws.length = 32 := hlen
    simp only [zeroStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
      RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true,
      inRw, hbase, haddr, true_and, and_true, hwslen]
    exact ⟨by omega, Nat.one_dvd _⟩
  case swdWriteBe32U64.loop2.inv_init =>
    rintro rf' ws' A'
      ⟨rf₁, ws₁, -, ⟨⟨i, -, hx10, hx11, hx6, hx5, hle, hlen, hws1⟩, hncond⟩, rfl, rfl⟩
    have hi32 : i = 32 := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx5, hx6] at hncond
      have : (BitVec.ofNat 64 i).toNat = (32 : Word).toNat := by rw [hncond]
      rw [show (32 : Word).toNat = 32 from by decide, BitVec.toNat_ofNat] at this
      omega
    subst hi32
    simp only [initBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem, beInv]
    refine ⟨?_, ?_, ?_, ?_, by omega, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]; exact hx10
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]; exact hx11
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]; rfl
    · rw [hws1, zeroWin_32_eq orig hlen, ← beWin32_zero v]
  case swdWriteBe32U64.loop2.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx11, hx6, hx5, -, hws0⟩, -⟩, rfl, rfl⟩
    simp only [hbase]
    rw [be_engine _ dst v rf₀ ws₀ i hi hx5 hx10 hx11]
    refine ⟨?_, ?_, ?_, ?_, by omega, ?_⟩
    · rw [beStepRf_get_x10]; exact hx10
    · rw [beStepRf_get_x11]; exact hx11
    · rw [beStepRf_get_x6]; exact hx6
    · rw [beStepRf_get_x5, hx5, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from by decide]
      omega
    · rw [hws0, beWin32_step v i hi]
  case swdWriteBe32U64.loop2.exhausted =>
    rintro rf ws A ⟨-, -, hx6, hx5, -, -⟩
    simp only [Cond.holds, hx5, hx6, not_not]
    decide
  case swdWriteBe32U64.loop2.body.be.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx10, hx11, hx6, hx5, -, -⟩, -⟩
    have haddr : (rf.get .x11 + signExtend12 (24 : BitVec 12) + rf.get .x5
        + signExtend12 (0 : BitVec 12) - dst).toNat = 24 + i := by
      rw [hx11, hx5, show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
        show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hwslen : ws.length = 32 := hlen
    simp only [beStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
      inRw, hbase, haddr, true_and, and_true, hwslen]
    exact ⟨by omega, Nat.one_dvd _⟩
  case swdWriteBe32U64.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx11, hx6, hx5, -, rfl⟩, hncond⟩
    have hi8 : i = 8 := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx5, hx6] at hncond
      have : (BitVec.ofNat 64 i).toNat = (8 : Word).toNat := by rw [hncond]
      rw [show (8 : Word).toNat = 8 from by decide, BitVec.toNat_ofNat] at this
      omega
    subst hi8
    exact beWin32_8_eq v

#print axioms swdWriteBe32U64Fn_spec

end SwdWriteBe32U64SAsm

end EvmAsm.Codegen
