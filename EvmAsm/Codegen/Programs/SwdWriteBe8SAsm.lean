/-
  EvmAsm.Codegen.Programs.SwdWriteBe8SAsm

  Verified SAsm port of `swd_write_be8` (bead evm-asm-4ch8f.12.8): write the
  u64 in `a0` big-endian into the 8 bytes at `a1`.

  Source (`swdWriteBe8_prog` in SystemWrites.lean): a fixed 8-iteration loop
  (`i = x5 : 0 → 8`) that, for each `i`, extracts the `i`-th big-endian byte
  of `a0` — `(a0 >>> (56 - 8*i)) &&& 0xff` — and stores it at `a1 + i`.

  Modelled as an SAsm `Fn` over a WRITABLE region `⟨a1, 8⟩` (the store value
  comes from the register `a0`, not memory, so there is no read-only region
  and no load — a plain `.block` body suffices, tracking the writable bytes
  `ws` directly through the loop invariant).

  Post pins ALL eight destination bytes to the big-endian encoding of `a0`
  (`ws = beBytes a0`, independent of the incoming `orig` bytes).

  The emitted routine is re-emitted from the verified structured loop.  Exact
  identity is kernel-pinned below
  (`swdWriteBe8Body … .flatten 0 ++ [ret] = swdWriteBe8_prog`).  This changes
  the old back-edge displacement from `-40` to `-36`, so EEST A/B is required.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.SystemWrites

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SwdWriteBe8SAsm

/-- The `k`-th big-endian byte of `v`: shift byte `k` (MSB-first) down to the
    bottom, mask, truncate.  Matches exactly the value the routine stores. -/
def beByte (v : Word) (k : Nat) : BitVec 8 :=
  BitVec.truncate 8 ((v >>> (56 - 8 * k)) &&& 255)

/-- The 8-byte big-endian encoding of `v`. -/
def beBytes (v : Word) : List (BitVec 8) :=
  (List.range 8).map (beByte v)

/-- Loop window: the first `i` bytes are already the big-endian bytes of `v`,
    the rest is the untouched tail of the original buffer. -/
def writeBe8Win (v : Word) (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (List.range i).map (beByte v) ++ orig.drop i

#guard writeBe8Win 0x0102030405060708 [0,0,0,0,0,0,0,0] 0 = [0,0,0,0,0,0,0,0]
#guard beBytes 0x0102030405060708 = [1, 2, 3, 4, 5, 6, 7, 8]

theorem writeBe8Win_zero (v : Word) (orig : List (BitVec 8)) :
    writeBe8Win v orig 0 = orig := by
  simp [writeBe8Win]

theorem writeBe8Win_8_eq (v : Word) (orig : List (BitVec 8)) (h : orig.length = 8) :
    writeBe8Win v orig 8 = beBytes v := by
  simp only [writeBe8Win, beBytes, List.drop_eq_nil_of_le (by omega : orig.length ≤ 8),
    List.append_nil]

theorem length_writeBe8Win (v : Word) (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 8) (hi : i ≤ 8) :
    (writeBe8Win v orig i).length = 8 := by
  simp only [writeBe8Win, List.length_append, List.length_map, List.length_range,
    List.length_drop, h]
  omega

/-- One step: replacing element `i` of the window with `beByte v i` extends the
    already-encoded prefix by one. -/
theorem writeBe8Win_step (v : Word) (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 8) (hi : i < 8) :
    setBytes (writeBe8Win v orig i) i [beByte v i] = writeBe8Win v orig (i + 1) := by
  rw [setBytes_singleton]
  have hpre : ((List.range i).map (beByte v)).length = i := by simp
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [writeBe8Win, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]
  rw [hdrop]
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self,
    List.set_cons_zero]

def swdWriteBe8InitBlock : List Instr := [.LI .x5 0, .LI .x6 8]

def swdWriteBe8StepBlock : List Instr :=
  [.LI .x7 56,
   .SLLI .x28 .x5 3,
   .SUB .x7 .x7 .x28,
   .SRL .x29 .x10 .x7,
   .ANDI .x29 .x29 255,
   .ADD .x30 .x11 .x5,
   .SB .x30 .x29 0,
   .ADDI .x5 .x5 1]

def swdWriteBe8Inv (v dst : Word) (orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = v ∧ rf.get .x11 = dst ∧ rf.get .x6 = 8 ∧
    rf.get .x5 = BitVec.ofNat 64 i ∧
    i ≤ 8 ∧ orig.length = 8 ∧ ws = writeBe8Win v orig i

def swdWriteBe8Body (v dst : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init" swdWriteBe8InitBlock ;;;
  .«while» "loop" (.bne .x5 .x6) 8 (swdWriteBe8Inv v dst orig)
    (.block "step" swdWriteBe8StepBlock)

def swdWriteBe8Fn (v dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "swdWriteBe8"
  rw := ⟨dst, 8⟩
  pre := fun rf ws _ =>
    rf.get .x10 = v ∧ rf.get .x11 = dst ∧ ws = orig ∧ orig.length = 8
  post := fun _ ws _ => ws = beBytes v
  body := swdWriteBe8Body v dst orig

def swdWriteBe8_verified : Program :=
  (swdWriteBe8Body 0 0 []).flatten 0

#guard (swdWriteBe8_verified : List Instr).length = 12
#guard (swdWriteBe8Body 0 0 []).flatten 0 = (swdWriteBe8Body 0 0 []).flatten 0x80000000

-- Emitted instructions, pinned exactly.  The verified structured loop targets
-- the guard directly on its back-edge; `swdWriteBe8_prog` is re-emitted with
-- that `-36` displacement instead of the old hand-written `-40` displacement.
#guard (swdWriteBe8Body 0 0 []).flatten 0 =
  [.LI .x5 0, .LI .x6 8,
   .BEQ .x5 .x6 (40 : BitVec 13),
   .LI .x7 56, .SLLI .x28 .x5 3, .SUB .x7 .x7 .x28, .SRL .x29 .x10 .x7,
   .ANDI .x29 .x29 255, .ADD .x30 .x11 .x5, .SB .x30 .x29 0, .ADDI .x5 .x5 1,
   .JAL .x0 (-36 : BitVec 21)]
#guard (swdWriteBe8Body 0 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] =
  swdWriteBe8_prog

/-- The register file after one loop body (the six ALU results plus the
    counter bump; the store leaves registers unchanged). -/
def stepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x7 (56 : Word)
  let r2 := r1.set .x28 (r1.get .x5 <<< (3 : BitVec 6).toNat)
  let r3 := r2.set .x7 (r2.get .x7 - r2.get .x28)
  let r4 := r3.set .x29 (r3.get .x10 >>> ((r3.get .x7).toNat % 64))
  let r5 := r4.set .x29 (r4.get .x29 &&& signExtend12 (255 : BitVec 12))
  let r6 := r5.set .x30 (r5.get .x11 + r5.get .x5)
  r6.set .x5 (r6.get .x5 + signExtend12 (1 : BitVec 12))

theorem stepRf_get_x5 (rf : RegFile) :
    (stepRf rf).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold stepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem stepRf_get_x6 (rf : RegFile) : (stepRf rf).get .x6 = rf.get .x6 := by
  unfold stepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]

theorem stepRf_get_x10 (rf : RegFile) : (stepRf rf).get .x10 = rf.get .x10 := by
  unfold stepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28)]

theorem stepRf_get_x11 (rf : RegFile) : (stepRf rf).get .x11 = rf.get .x11 := by
  unfold stepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28)]

/-- The value the routine computes and stores at iteration `i` is exactly the
    `i`-th big-endian byte of `v`. -/
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

/-- Engine (own heartbeat budget): one loop body stores the `i`-th big-endian
    byte at offset `i` of the writable region and advances the counter. -/
theorem step_engine (reg : Region) (dst v : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 8)
    (hx5 : rf.get .x5 = BitVec.ofNat 64 i) (hx10 : rf.get .x10 = v)
    (hx11 : rf.get .x11 = dst) :
    execBlock reg dst rf ws swdWriteBe8StepBlock
      = (stepRf rf, setBytes ws i [beByte v i]) := by
  have haddr : (rf.get .x11 + rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [hx11, hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  · rfl
  · show setBytes ws ((rf.get .x11 + rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat)
        [BitVec.truncate 8 ((rf.get .x10 >>>
            ((56 - rf.get .x5 <<< (3 : BitVec 6).toNat).toNat % 64)) &&& signExtend12 255)]
      = setBytes ws i [beByte v i]
    rw [haddr, hx10, hx5, store_val_eq_beByte v i hi]

theorem swdWriteBe8Fn_spec (v dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 8⟩) (base : Word) :
    (swdWriteBe8Fn v dst orig).Spec base := by
  have hnowrap : dst.toNat + 8 < 2 ^ 64 := hwf.2.1
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case swdWriteBe8.loop.inv_init =>
    rintro rf' ws' A' ⟨rf₀, ws₀, -, ⟨hx10, hx11, hws0, hlen⟩, rfl, rfl⟩
    simp only [swdWriteBe8InitBlock, execBlock_cons, execBlock_nil, execInstrRF,
      aluSem, swdWriteBe8Inv]
    refine ⟨?_, ?_, ?_, ?_, by omega, hlen, hws0.trans (writeBe8Win_zero v orig).symm⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]; exact hx10
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]; exact hx11
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]; rfl
  case swdWriteBe8.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx11, hx6, hx5, -, hlen, hws0⟩, -⟩, rfl, rfl⟩
    simp only [show (swdWriteBe8Fn v dst orig).rw.base = dst from rfl]
    rw [step_engine _ dst v rf₀ ws₀ i hi hx5 hx10 hx11]
    refine ⟨?_, ?_, ?_, ?_, by omega, hlen, ?_⟩
    · rw [stepRf_get_x10]; exact hx10
    · rw [stepRf_get_x11]; exact hx11
    · rw [stepRf_get_x6]; exact hx6
    · rw [stepRf_get_x5, hx5, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from by decide]
      omega
    · rw [hws0, writeBe8Win_step v orig i hlen hi]
  case swdWriteBe8.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx6, hx5, -, -, -⟩
    simp only [Cond.holds, hx5, hx6, not_not]
    decide
  case swdWriteBe8.loop.body.step.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx10, hx11, hx6, hx5, -, -, -⟩, -⟩
    have hbase : (swdWriteBe8Fn v dst orig).rw.base = dst := rfl
    have haddr : (rf.get .x11 + rf.get .x5 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
      rw [hx11, hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hwslen : ws.length = 8 := hlen
    simp only [swdWriteBe8StepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
      inRw, hbase, haddr, true_and, and_true, hwslen]
    exact ⟨by omega, Nat.one_dvd _⟩
  case swdWriteBe8.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx11, hx6, hx5, -, hlen, rfl⟩, hncond⟩
    have hi8 : i = 8 := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx5, hx6] at hncond
      have h8 : (8 : Word).toNat = 8 := by decide
      have : (BitVec.ofNat 64 i).toNat = (8 : Word).toNat := by rw [hncond]
      rw [h8, BitVec.toNat_ofNat] at this
      omega
    subst hi8
    exact writeBe8Win_8_eq v orig hlen

#print axioms swdWriteBe8Fn_spec

end SwdWriteBe8SAsm

end EvmAsm.Codegen
