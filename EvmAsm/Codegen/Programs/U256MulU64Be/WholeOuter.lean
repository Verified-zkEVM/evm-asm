import EvmAsm.Codegen.Programs.U256MulU64Be.WholeRipple

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm Rv64.SAsm.Stmt

def highBase
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m : Nat)
    (accBytes : List (BitVec 8)) (ptr carry : Word) : Assertion :=
  outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
    ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
    ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 ((m % 2 ^ 64) / 256 ^ 8)) **
    ((.x28 : Reg) ↦ᵣ ptr) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
    ((.x30 : Reg) ↦ᵣ carry) ** bytesRegion accBase accBytes

def highSum (aBytes : List (BitVec 8)) (b : Word) (i m : Nat) : Nat :=
  m / 2 ^ 64 + mulCarry (mulState aBytes b i) (m % 2 ^ 64) i 8 +
    ((rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8).getD (i + 8) 0).toNat

def highAcc (aBytes : List (BitVec 8)) (b : Word) (i m : Nat) :
    List (BitVec 8) :=
  let acc := rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8
  acc.set (i + 8) (BitVec.ofNat 8 (highSum aBytes b i m))

def highByte (aBytes : List (BitVec 8)) (b : Word) (i m : Nat) : Word :=
  BitVec.ofNat 64 (highSum aBytes b i m % 256)

def highCarry (aBytes : List (BitVec 8)) (b : Word) (i m : Nat) : Word :=
  BitVec.ofNat 64 (highSum aBytes b i m / 256)

theorem getD_set_ne_local {l : List (BitVec 8)} {i j : Nat}
    {b d : BitVec 8} (h : i ≠ j) :
    (l.set i b).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

theorem mulState_getD_ge
    (aBytes : List (BitVec 8)) (b : Word) :
    ∀ i j, i + 8 ≤ j → (mulState aBytes b i).getD j 0 = 0 := by
  intro i
  induction i with
  | zero =>
      intro j hj
      rw [mulState, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
  | succ i ih =>
      intro j hj
      rw [mulState]
      dsimp [mulOuterStep]
      split
      · exact ih j (by omega)
      · calc
          _ = (mulState aBytes b i).getD j 0 := by
            rw [getD_set_ne_local (by omega)]
            exact getD_rippleState_of_ge _ _ _ 8 j (by omega)
          _ = 0 := ih j (by omega)

theorem high_truncate_ofNat (n : Nat) :
    (BitVec.ofNat 64 n).truncate 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j
  simp

theorem highBody_exact
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (_hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m : Nat) (hi : i < 32)
    (hbyte : byte.toNat < 256) (hmul : m = byte.toNat * b.toNat)
    (old13 old31 : Word) :
    cpsTripleWithin 7 (mulBase + 172) (mulBase + 200) mulCR
      (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m 8 ** ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ old31))
      (highBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m (highAcc aBytes b i m)
        (accBase + BitVec.ofNat 64 (i + 9)) (highCarry aBytes b i m) **
        ((.x13 : Reg) ↦ᵣ (highByte aBytes b i m)) **
        ((.x31 : Reg) ↦ᵣ (BitVec.ofNat 64 (highSum aBytes b i m)))) := by
  let accE := mulState aBytes b i
  let M0 := m % 2 ^ 64
  let accK := rippleState accE M0 i 8
  let ptr := accBase + BitVec.ofNat 64 (i + 8)
  let oldNat := (accK.getD (i + 8) 0).toNat
  let highNat := m / 2 ^ 64 + mulCarry accE M0 i 8 + oldNat
  let oldW := (accK.getD (i + 8) 0).zeroExtend 64
  let highW := BitVec.ofNat 64 highNat
  let newW := BitVec.ofNat 64 (highNat % 256)
  let carryW := BitVec.ofNat 64 (highNat / 256)
  let nextAcc := accK.set (i + 8) (BitVec.ofNat 8 highNat)
  let nextPtr := accBase + BitVec.ofNat 64 (i + 9)
  let S : Assertion :=
    outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (M0 / 256 ^ 8)) **
      ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ
        (BitVec.ofNat 64 (mulCarry accE M0 i 8)))
  let S1 : Assertion :=
    outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (M0 / 256 ^ 8)) **
      ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ
        (BitVec.ofNat 64 (mulCarry accE M0 i 8)))
  let S2 : Assertion :=
    outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (M0 / 256 ^ 8)) **
      ((.x29 : Reg) ↦ᵣ (0 : Word))
  have hacc : accE.length = 40 := by
    have hs : ∀ j : Nat, (mulState aBytes b j).length = 40 := by
      intro j
      induction j with
      | zero => simp [mulState]
      | succ j ih =>
          dsimp [mulState, mulOuterStep]
          split
          · exact ih
          · rw [List.length_set, length_rippleState, ih]
    exact hs i
  have hiacc : i + 8 < accE.length := by rw [hacc]; omega
  have haccK : accK.length = 40 := by
    dsimp [accK]
    rw [length_rippleState, hacc]
  have hvalid := accBase_valid_byte (i + 8) (by omega)
  have hover := accBase_no_overflow (i + 8) (by omega)
  have hm : m < 256 * 2 ^ 64 := by
    by_cases hz : byte.toNat = 0
    · rw [hmul, hz, Nat.zero_mul]
      omega
    · have hb : byte.toNat * b.toNat < byte.toNat * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_left b.isLt (Nat.pos_of_ne_zero hz)
      have hb' : byte.toNat * 2 ^ 64 < 256 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hbyte (by positivity)
      rw [hmul]
      exact lt_trans hb hb'
  have hmhi : m / 2 ^ 64 < 256 := by omega
  have hcarry : mulCarry accE M0 i 8 ≤ 1 := mulCarry_le_one accE M0 i 8
  have hold : oldNat < 256 := by
    dsimp [oldNat]
    exact (accK.getD (i + 8) 0).isLt
  have hhigh : highNat < 2 ^ 64 := by
    dsimp [highNat]
    omega
  have hmask : highW &&& BitVec.ofNat 64 255 = newW := by
    dsimp [highW, newW]
    exact word_and255_ofNat highNat hhigh
  have hshift : highW >>> 8 = carryW := by
    apply BitVec.eq_of_toNat_eq
    dsimp [highW, carryW]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhigh,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : highNat / 256 < 2 ^ 64)]
    simp [Nat.shiftRight_eq_div_pow, show 2 ^ 8 = 256 by decide]
  have hset :
      (BitVec.setWidth 8 newW) = BitVec.ofNat 8 highNat := by
    dsimp [newW]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  have hsum : highW = BitVec.ofNat 64 highNat := by rfl
  have hstate :
      nextAcc = accK.set (i + 8) (BitVec.setWidth 8 newW) := by
    dsimp [nextAcc]
    rw [hset]
  have hptr :
      ptr + 1 = nextPtr := by
    dsimp [ptr, nextPtr]
    rw [BitVec.add_assoc]
    congr 1
    bv_omega
  have hS : S.pcFree := by
    dsimp [S, outerStableNoAcc]
    apply pcFree_sepConj
    · apply pcFree_sepConj
      · exact hF
      · pcf
    · pcf
  have hS1 : S1.pcFree := by
    dsimp [S1, outerStableNoAcc]
    apply pcFree_sepConj
    · apply pcFree_sepConj
      · exact hF
      · pcf
    · pcf
  have hS2 : S2.pcFree := by
    dsimp [S2, outerStableNoAcc]
    apply pcFree_sepConj
    · apply pcFree_sepConj
      · exact hF
      · pcf
    · pcf
  have hget : accK.getD (i + 8) 0 = accK[i + 8]'(by rw [haccK]; omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    rfl
  have h0raw := bytesRegion_lbu_within .x31 .x28 accBase old31
    (mulBase + 172) accK (i + 8) (by decide) accBase_align
    (by omega) hover hvalid
  have h0e := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem) h0raw
  have h0f := cpsTripleWithin_frameR
    (S ** ((.x13 : Reg) ↦ᵣ old13)) (pcFree_sepConj hS (by pcf)) h0e
  have h0 : cpsTripleWithin 1 (mulBase + 172) (mulBase + 176) mulCR
      (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m 8 ** ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ old31))
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ oldW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [rippleBase, S, accK, ptr, M0, outerStableNoAcc] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [S, ptr, M0, oldW] at hq ⊢
      rw [← hget] at hq
      xperm_hyp hq) h0f
  have h1raw := add_spec_gen_rd_eq_rs1_within .x31 .x7 oldW
    (BitVec.ofNat 64 (m / 2 ^ 64)) (mulBase + 176) (by decide)
  rw [show (mulBase + 176 : Word) + 4 = mulBase + 180 from by decide] at h1raw
  have h1e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h1raw
  have h1f := cpsTripleWithin_frameR
    (S1 ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
      ((.x13 : Reg) ↦ᵣ old13)) (pcFree_sepConj hS1 (by pcf)) h1e
  have h1 : cpsTripleWithin 1 (mulBase + 176) (mulBase + 180) mulCR
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ oldW))
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ (oldW +
          BitVec.ofNat 64 (m / 2 ^ 64)))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [S, S1] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [S, S1] at hq ⊢
      xperm_hyp hq) h1f
  have h1val :
      oldW + BitVec.ofNat 64 (m / 2 ^ 64) = BitVec.ofNat 64 (oldNat + m / 2 ^ 64) := by
    have holdNatW : oldW.toNat = oldNat := by
      dsimp [oldW, oldNat]
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by omega : (accK.getD (i + 8) 0).toNat < 2 ^ 64)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [BitVec.toNat_ofNat]
    rw [holdNatW]
    omega
  have h1' := cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      rw [h1val] at hq
      exact hq) h1
  have h2raw := add_spec_gen_rd_eq_rs1_within .x31 .x30
    (BitVec.ofNat 64 (oldNat + m / 2 ^ 64))
    (BitVec.ofNat 64 (mulCarry accE M0 i 8)) (mulBase + 180) (by decide)
  rw [show (mulBase + 180 : Word) + 4 = mulBase + 184 from by decide] at h2raw
  have h2e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h2raw
  have h2f := cpsTripleWithin_frameR
    (S2 ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
      ((.x13 : Reg) ↦ᵣ old13)) (pcFree_sepConj hS2 (by pcf)) h2e
  have h2val :
      BitVec.ofNat 64 (oldNat + m / 2 ^ 64) +
        BitVec.ofNat 64 (mulCarry accE M0 i 8) = highW := by
    dsimp [highW, highNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hsum64 : oldNat + m / 2 ^ 64 < 2 ^ 64 := by omega
    have hsum64' : oldNat + m / 18446744073709551616 < 2 ^ 64 := by
      simpa using hsum64
    have hcarry64 : mulCarry accE M0 i 8 < 2 ^ 64 := by omega
    have htotal64' : oldNat + m / 18446744073709551616 +
        mulCarry accE M0 i 8 < 2 ^ 64 := by
      simpa using (show oldNat + m / 2 ^ 64 + mulCarry accE M0 i 8 < 2 ^ 64 by
        omega)
    simp only [Nat.mod_eq_of_lt hsum64', Nat.mod_eq_of_lt hcarry64,
      Nat.mod_eq_of_lt htotal64']
    dsimp [highNat]
    omega
  have h2 : cpsTripleWithin 1 (mulBase + 180) (mulBase + 184) mulCR
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ old13) **
        ((.x31 : Reg) ↦ᵣ (BitVec.ofNat 64 (oldNat + m / 2 ^ 64))))
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ highW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [S, S2] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      rw [h2val] at hq
      dsimp [S, S2] at hq ⊢
      xperm_hyp hq) h2f
  have h3raw := andi_spec_gen_within .x13 .x31 old13 highW
    (255 : BitVec 12) (mulBase + 184) (by decide)
  rw [show (mulBase + 184 : Word) + 4 = mulBase + 188 from by decide,
    show Rv64.signExtend12 (255 : BitVec 12) = (255 : Word) from by decide] at h3raw
  have h3e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h3raw
  have h3f := cpsTripleWithin_frameR
    (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK)
      (pcFree_sepConj hS (by pcf)) h3e
  have h3 : cpsTripleWithin 1 (mulBase + 184) (mulBase + 188) mulCR
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ highW))
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ highW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        have hmask' : highW &&& (255 : Word) = newW := by
          change highW &&& BitVec.ofNat 64 255 = newW
          exact hmask
        rw [hmask'] at hq
        xperm_hyp hq) h3f
  have h4raw := bytesRegion_sb_within .x28 .x13 accBase newW
    (mulBase + 188) accK (i + 8) accBase_align (by rw [haccK]; omega)
    hover hvalid
  have hstate' : accK.set (i + 8) (BitVec.truncate 8 newW) = nextAcc := by
    change accK.set (i + 8) (BitVec.setWidth 8 newW) = nextAcc
    exact hstate.symm
  rw [show (mulBase + 188 : Word) + 4 = mulBase + 192 from by decide,
    hstate'] at h4raw
  have h4e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h4raw
  have h4f := cpsTripleWithin_frameR
    (S ** ((.x31 : Reg) ↦ᵣ highW)) (pcFree_sepConj hS (by pcf)) h4e
  have h4 := h4f
  have h5raw := srli_spec_gen_within .x30 .x31
    (BitVec.ofNat 64 (mulCarry accE M0 i 8)) highW (8 : BitVec 6)
    (mulBase + 192) (by decide)
  rw [show (mulBase + 192 : Word) + 4 = mulBase + 196 from by decide] at h5raw
  change cpsTripleWithin 1 _ _ _ _
    (((.x31 : Reg) ↦ᵣ highW) **
      ((.x30 : Reg) ↦ᵣ (highW >>> 8))) at h5raw
  rw [hshift] at h5raw
  have h5e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h5raw
  have h5f := cpsTripleWithin_frameR
    (S2 ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase nextAcc **
      ((.x13 : Reg) ↦ᵣ newW)) (pcFree_sepConj hS2 (by pcf)) h5e
  have h5 := h5f
  have h6raw := addi_spec_gen_same_within .x28 ptr
    (1 : BitVec 12) (mulBase + 196) (by decide)
  rw [show (mulBase + 196 : Word) + 4 = mulBase + 200 from by decide,
    show Rv64.signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    hptr] at h6raw
  have h6e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h6raw
  have h6f := cpsTripleWithin_frameR
    (S2 ** ((.x30 : Reg) ↦ᵣ carryW) ** bytesRegion accBase nextAcc **
      ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ highW))
      (pcFree_sepConj hS2 (by pcf)) h6e
  have h6 := h6f
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0 h1'
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq1 h2
  have hseq3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq2 h3
  have hseq4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq3 h4
  have hseq5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq4 h5
  have hseq6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq5 h6
  have hpost := highBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
      i byte m nextAcc nextPtr carryW
  refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [rippleBase, highBase, S, accE, M0, accK, ptr] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [highBase, highAcc, highCarry, highByte, highSum, S, S2, accE,
        M0, accK, ptr, nextAcc, nextPtr, carryW, newW, highW, highNat,
        oldNat] at hq ⊢
      simp only [List.getD_eq_getElem?_getD] at hq ⊢
      norm_num at hq ⊢
      xperm_hyp hq) hseq6

/-! The outer back-edge is a small cyclic continuation shared by the zero and
nonzero arms.  Keeping it separate makes the arm proofs end at the same
header guard, rather than hiding the `JAL`/header reload in an arm-specific
alias. -/

theorem outerNext_spec
    (P : Assertion) (hP : P.pcFree) (i : Nat) (hi : i < 32) :
    cpsTripleWithin 3 (mulBase + 232) (mulBase + 84) mulCR
      (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** regOwn .x5 ** P)
      (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        ((.x5 : Reg) ↦ᵣ (32 : Word)) ** P) := by
  have haddi := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (addi_spec_gen_same_within .x20 (BitVec.ofNat 64 i)
      (1 : BitVec 12) (mulBase + 232) (by decide))
  rw [show mulBase + 232 + 4 = mulBase + 236 from by decide,
    show Rv64.signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at haddi
  have hctr : BitVec.ofNat 64 i + (1 : Word) = BitVec.ofNat 64 (i + 1) := by
    simpa only [show Rv64.signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      using outerCtr_succ i hi
  rw [hctr] at haddi
  have haddiF := cpsTripleWithin_frameR
    (regOwn .x5 ** P) (pcFree_sepConj pcFree_regOwn hP) haddi
  have hjal := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (jal_x0_spec_gen_within (-156 : BitVec 21) (mulBase + 236))
  rw [show mulBase + 236 + Rv64.signExtend21 (-156 : BitVec 21) = mulBase + 80 from by decide]
    at hjal
  have hjalF := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) ** regOwn .x5 ** P)
    (pcFree_sepConj (by pcf) (pcFree_sepConj pcFree_regOwn hP)) hjal
  rw [sepConj_emp_left'] at hjalF
  have hli := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_own_within .x5 (32 : Word) (mulBase + 80) (by decide))
  rw [show mulBase + 80 + 4 = mulBase + 84 from by decide] at hli
  have hliF := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) ** P)
    (pcFree_sepConj (by pcf) hP) hli
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
    xperm_hyp hp)
    haddiF hjalF
  have hseq' := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
    xperm_hyp hp)
    hseq hliF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq'

/-! The high-byte add proves that the ninth byte is below `2^64`, hence the
carry register is zero.  The emitted `while` still has its branch arm, so the
proof consumes that arm explicitly and rejects the unreachable body rather
than silently treating the loop as absent. -/

theorem carrySkip_spec
    (P : Assertion) (hP : P.pcFree) (carry : Word) (hcarry : carry = 0) :
    cpsTripleWithin 1 (mulBase + 200) (mulBase + 232) mulCR
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** P ** ((.x30 : Reg) ↦ᵣ carry))
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** P ** ((.x30 : Reg) ↦ᵣ carry)) := by
  have hbr := cpsBranchWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (beq_spec_gen_within .x30 .x0 (32 : BitVec 13) carry (0 : Word)
      (mulBase + 200))
  rw [show mulBase + 200 + Rv64.signExtend13 (32 : BitVec 13) = mulBase + 232 from by decide,
    show mulBase + 200 + 4 = mulBase + 204 from by decide] at hbr
  have hbrF := cpsBranchWithin_frameR P hP hbr
  have htaken := cpsBranchWithin_takenPath hbrF (fun _ hq => by
    obtain ⟨h1, _, _, _, hpure, _⟩ := hq
    have hpure' : ((((.x30 : Reg) ↦ᵣ carry) **
        ((.x0 : Reg) ↦ᵣ (0 : Word))) ** ⌜carry ≠ 0⌝) h1 :=
      (sepConj_assoc h1).mpr hpure
    exact (sepConj_pure_right _).1 hpure' |>.2 hcarry)
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun s hq => ?_) htaken
  have hpure_to_emp : ∀ h, (⌜carry = 0⌝) h → empAssertion h := by
    intro h hp
    change h = PartialState.empty ∧ carry = 0 at hp
    exact hp.1
  obtain ⟨h1, h2, hd, hu, hleft, hP⟩ := hq
  have hleft' := sepConj_mono_right
    (sepConj_mono_right hpure_to_emp) h1 hleft
  rw [sepConj_emp_right'] at hleft'
  have hq' : ((((.x30 : Reg) ↦ᵣ carry) **
      ((.x0 : Reg) ↦ᵣ (0 : Word))) ** P) s :=
    ⟨h1, h2, hd, hu, hleft', hP⟩
  xperm_hyp hq'

/-! The complete nonzero arm: initializer, eight-byte ripple, high-byte
addition, dead carry path, and the common back-edge. -/

theorem mulNonzero_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (hi : i < 32) (byte : Word) (hbyte : byte.toNat < 256)
    (hbyte_ne : byte ≠ 0)
    (hbyte_input : byte = (aBytes[31 - i]'(by rw [hlen]; omega)).zeroExtend 64)
    (m : Nat) (hmul : m = byte.toNat * b.toNat) :
    cpsTripleWithin 104 (mulBase + 108) (mulBase + 84) mulCR
      (((.x5 : Reg) ↦ᵣ byte) ** ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i)
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr (i + 1)) := by
  have hbyte_le : byte.toNat ≤ 255 := by omega
  have hinit := mulInit_spec F hF aBytes
    spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte hbyte_le m hmul
  have hinit' : cpsTripleWithin 5 (mulBase + 108) (mulBase + 128) mulCR
      (((.x5 : Reg) ↦ᵣ byte) ** ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i)
      (((.x29 : Reg) ↦ᵣ (8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m 0) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hinit
    dsimp [rippleBase, rippleLoopInv, outerStableNoAcc, outerStableNoX0]
      at hq ⊢
    xperm_hyp hq
  have hloop := rippleLoop_spec F hF aBytes hlen
    spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m hi
  have hloop' : cpsTripleWithin 88 (mulBase + 128) (mulBase + 172) mulCR
      (((.x29 : Reg) ↦ᵣ (8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m 0)
      (((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m 8) :=
    hloop
  have hhigh : cpsTripleWithin 7 (mulBase + 172) (mulBase + 200) mulCR
      (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m 8 ** regOwn .x13 ** regOwn .x31)
      (highBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m (highAcc aBytes b i m)
        (accBase + BitVec.ofNat 64 (i + 9)) (highCarry aBytes b i m) **
        regOwn .x13 ** regOwn .x31) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x13) (r2 := .x31)
      (P := rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m 8) ?_
    intro old13 old31
    have h := highBody_exact F hF aBytes hlen
      spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m hi hbyte hmul old13 old31
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) h
    have hq' := sepConj_mono
      (P := highBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m (highAcc aBytes b i m)
        (accBase + BitVec.ofNat 64 (i + 9)) (highCarry aBytes b i m))
      (P' := highBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m (highAcc aBytes b i m)
        (accBase + BitVec.ofNat 64 (i + 9)) (highCarry aBytes b i m))
      (Q := ((.x13 : Reg) ↦ᵣ (highByte aBytes b i m)) **
        ((.x31 : Reg) ↦ᵣ (BitVec.ofNat 64 (highSum aBytes b i m))))
      (Q' := regOwn .x13 ** regOwn .x31)
      (fun _ h => h)
      (sepConj_mono (regIs_to_regOwn .x13 (highByte aBytes b i m))
        (regIs_to_regOwn .x31 (BitVec.ofNat 64 (highSum aBytes b i m)))) s hq
    simpa only [sepConj_assoc'] using hq'
  have hm : m < 256 * 2 ^ 64 := by
    by_cases hz : byte.toNat = 0
    · rw [hmul, hz, Nat.zero_mul]
      omega
    · have hb : byte.toNat * b.toNat < byte.toNat * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_left b.isLt (Nat.pos_of_ne_zero hz)
      have hb' : byte.toNat * 2 ^ 64 < 256 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hbyte (by positivity)
      rw [hmul]
      exact lt_trans hb hb'
  have hmhi : m / 2 ^ 64 < 256 := by omega
  have hcarry_le : mulCarry (mulState aBytes b i) (m % 2 ^ 64) i 8 ≤ 1 :=
    mulCarry_le_one _ _ _ _
  have hacc : (mulState aBytes b i).length = 40 := by
    have hs : ∀ j : Nat, (mulState aBytes b j).length = 40 := by
      intro j
      induction j with
      | zero => simp [mulState]
      | succ j ih =>
          dsimp [mulState, mulOuterStep]
          split
          · exact ih
          · rw [List.length_set, length_rippleState, ih]
    exact hs i
  have hrip_len :
      (rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8).length = 40 := by
    rw [length_rippleState, hacc]
  have hidx : i + 8 <
      (rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8).length := by
    rw [hrip_len]
    omega
  have hold :
      ((rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8).getD
        (i + 8) 0).toNat < 256 := by
    have hget :
        (rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8).getD
            (i + 8) 0 =
          (rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8)[i + 8]'hidx := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
      rfl
    rw [hget]
    exact (rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8)[i + 8]'hidx |>.isLt
  have hacc_zero : (mulState aBytes b i).getD (i + 8) 0 = 0 :=
    mulState_getD_ge aBytes b i (i + 8) (by omega)
  have hrip_zero :
      (rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8).getD (i + 8) 0 = 0 := by
    rw [getD_rippleState_of_ge (mulState aBytes b i) (m % 2 ^ 64) i 8
      (i + 8) (by omega), hacc_zero]
  have hmulhi : m / 2 ^ 64 ≤ 254 := by
    simpa [hmul] using mulhu_le_254 byte b hbyte_le
  have hsum_eq : highSum aBytes b i m =
      m / 2 ^ 64 + mulCarry (mulState aBytes b i) (m % 2 ^ 64) i 8 := by
    dsimp [highSum]
    have hrip_zero_nat :
        ((rippleState (mulState aBytes b i) (m % 2 ^ 64) i 8).getD
            (i + 8) 0).toNat = 0 := by
      simpa using congrArg (fun x : BitVec 8 => x.toNat) hrip_zero
    have hrip_zero_nat' :
        ((rippleState (mulState aBytes b i) (m % 18446744073709551616) i 8).getD
            (i + 8) 0).toNat = 0 := by
      simpa using hrip_zero_nat
    have hrip_zero_opt :
        (((rippleState (mulState aBytes b i) (m % 18446744073709551616) i 8)[i + 8]?).getD
            (0 : BitVec 8)).toNat = 0 := by
      simpa only [List.getD_eq_getElem?_getD] using hrip_zero_nat'
    have hrip_zero_opt' :
        (((rippleState (mulState aBytes b i) (m % 18446744073709551616) i 8)[i + 8]?).getD
            (0#8 : BitVec 8)).toNat = 0 := by
      simpa using hrip_zero_opt
    simp only [List.getD_eq_getElem?_getD]
    rw [hrip_zero_opt']
    simp
  have hcarry_zero : highCarry aBytes b i m = (0 : Word) := by
    dsimp [highCarry]
    have hzero :
        (m / 2 ^ 64 + mulCarry (mulState aBytes b i) (m % 2 ^ 64) i 8) / 256 = 0 :=
      mulhu_add_carry_zero _ _ hmulhi hcarry_le
    rw [hsum_eq, hzero]
  have hbyte_nat :
      (aBytes[31 - i]'(by rw [hlen]; omega)).toNat = byte.toNat := by
    have ha : (aBytes[31 - i]'(by rw [hlen]; omega)).toNat < 2 ^ 64 := by
      have := (aBytes[31 - i]'(by rw [hlen]; omega)).isLt
      omega
    have ha' : (aBytes[31 - i]'(by rw [hlen]; omega)).toNat <
        18446744073709551616 := by simpa using ha
    simpa [Nat.mod_eq_of_lt ha'] using
      (congrArg (fun x : Word => x.toNat) hbyte_input).symm
  have hbyte_input_ne : aBytes[31 - i]'(by rw [hlen]; omega) ≠ 0 := by
    intro hz
    apply hbyte_ne
    rw [hbyte_input, hz]
    rfl
  have hstep : highAcc aBytes b i m = mulState aBytes b (i + 1) := by
    rw [mulState]
    simp only [mulOuterStep, highAcc]
    have hgetD : aBytes.getD (31 - i) (0#8 : BitVec 8) =
        aBytes[31 - i]'(by rw [hlen]; omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
      rfl
    have hgetD_nat :
        (aBytes.getD (31 - i) (0 : BitVec 8)).toNat =
          (aBytes[31 - i]'(by rw [hlen]; omega)).toNat := by
      exact congrArg BitVec.toNat hgetD
    split
    · apply False.elim (hbyte_input_ne ?_)
      rw [← hgetD]
      exact ‹_›
    · rw [hgetD_nat, hbyte_nat, ← hmul, hsum_eq, hrip_zero]
      congr 1
  let carryP : Assertion :=
    outerStableNoX0 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 ((m % 2 ^ 64) / 256 ^ 8)) **
      ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (i + 9))) **
      ((.x29 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion accBase (highAcc aBytes b i m) **
      regOwn .x13 ** regOwn .x31
  have hhigh' : cpsTripleWithin 7 (mulBase + 172) (mulBase + 200) mulCR
      (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m 8 ** regOwn .x13 ** regOwn .x31)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** carryP **
        ((.x30 : Reg) ↦ᵣ (highCarry aBytes b i m))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hhigh
    dsimp [carryP, highBase, outerStableNoAcc, outerStableNoX0]
      at hq ⊢
    xperm_hyp hq
  have hcarryP : carryP.pcFree := by
    dsimp [carryP, outerStableNoX0]
    have hstable :
        (outerStableNoX0 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr).pcFree := by
      dsimp [outerStableNoX0]
      exact pcFree_sepConj hF (by pcf)
    exact pcFree_sepConj hstable (by pcf)
  have hcarry := carrySkip_spec carryP hcarryP
    (highCarry aBytes b i m) hcarry_zero
  let nextP : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      outerStableNoX0 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 ((m % 2 ^ 64) / 256 ^ 8)) **
      ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (i + 9))) **
      ((.x29 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion accBase (highAcc aBytes b i m) **
      ((.x30 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x31
  have hnextP : nextP.pcFree := by
    dsimp [nextP, outerStableNoX0]
    have hstable :
        (outerStableNoX0 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr).pcFree := by
      dsimp [outerStableNoX0]
      exact pcFree_sepConj hF (by pcf)
    exact pcFree_sepConj (by pcf) (pcFree_sepConj hstable (by pcf))
  have hcarry' :
      cpsTripleWithin 1 (mulBase + 200) (mulBase + 232) mulCR
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** carryP **
          ((.x30 : Reg) ↦ᵣ (highCarry aBytes b i m)))
        (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) ** nextP) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hcarry
    simp only [carryP, nextP] at hq ⊢
    rw [show highCarry aBytes b i m = (0 : Word) from hcarry_zero] at hq
    xperm_hyp hq
  have hnextConcrete :
      cpsTripleWithin 3 (mulBase + 232) (mulBase + 84) mulCR
        (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) ** nextP)
        (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
          ((.x5 : Reg) ↦ᵣ (32 : Word)) ** nextP) := by
    have h := outerNext_spec nextP hnextP i hi
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => hq) h
    have hp' := sepConj_mono_right
      (sepConj_mono_left (regIs_to_regOwn .x5 byte)) _ hp
    xperm_hyp hp'
  have hloopHigh :
      cpsTripleWithin 88 (mulBase + 128) (mulBase + 172) mulCR
        (((.x29 : Reg) ↦ᵣ (8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
            i byte m 0)
        (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
            i byte m 8 ** regOwn .x13 ** regOwn .x31) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hloop'
    dsimp [rippleLoopInv, rippleBase, outerStableNoAcc, outerStableNoX0]
      at hq ⊢
    xperm_hyp hq
  have hseqInit := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hinit' hloopHigh
  have hseqHigh := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseqInit hhigh'
  have hseqCarry := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseqHigh hcarry'
  have hseqNext := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseqCarry hnextConcrete
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => ?_) hseqNext
  dsimp [nextP, outerHeaderInv, outerLoopInv, outerStableNoX0] at hq ⊢
  rw [hstep] at hq
  have hq' := sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (regIs_to_regOwn .x7 _)
            (sepConj_mono (regIs_to_regOwn .x6 _)
              (sepConj_mono (regIs_to_regOwn .x28 _)
                (sepConj_mono (regIs_to_regOwn .x29 _)
                  (sepConj_mono (fun _ h => h)
                    (sepConj_mono (regIs_to_regOwn .x30 _)
                      (fun _ h => h)))))))))) _ hq
  xperm_hyp hq'

/-! The outer branch consumes the byte loaded by `outerBytePrefix_spec`.
    Keeping the zero and nonzero continuations at the same exit makes the
    branch merge a genuine single-cycle triple; the zero arm is padded only
    to the nonzero arm's bound, not given a weaker semantic post. -/

theorem outerCycle_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (hi : i < 32)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + (31 - i) < 2 ^ 64)
    (hvalidA : isValidByteAccess (aPtr + BitVec.ofNat 64 (31 - i)) = true) :
    cpsTripleWithin 109 (mulBase + 88) (mulBase + 84) mulCR
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i)
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr (i + 1)) := by
  let byte : Word := (aBytes[31 - i]'(by omega)).zeroExtend 64
  let P : Assertion := outerLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i
  let P0 : Assertion :=
    outerStableNoX0 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion accBase (mulState aBytes b i)
  have hP : P.pcFree := by
    dsimp [P, outerLoopInv]
    exact pcFree_sepConj hF (by pcf)
  have hP0 : P0.pcFree := by
    have hstable : (outerStableNoX0 F aBytes spNew vRa v8 v9 v18 v19 v20
        aPtr b outPtr).pcFree := by
      dsimp [outerStableNoX0]
      exact pcFree_sepConj hF (by pcf)
    dsimp [P0]
    exact pcFree_sepConj hstable (by pcf)
  have hprefix := outerBytePrefix_spec F hF aBytes hlen
    spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i hi halignA hoverA hvalidA
  have hprefix' : cpsTripleWithin 4 (mulBase + 88) (mulBase + 104) mulCR
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i)
      (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        ((.x5 : Reg) ↦ᵣ byte) ** P) := by
    simpa only [byte, P] using hprefix
  have hbeq := cpsBranchWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := beq_spec_gen_within .x5 .x0 (128 : BitVec 13)
      byte (0 : Word) (mulBase + 104))
  rw [show mulBase + 104 + Rv64.signExtend13 (128 : BitVec 13) = mulBase + 232 from by decide,
    show mulBase + 104 + 4 = mulBase + 108 from by decide] at hbeq
  have hbeqF := cpsBranchWithin_frameR
    (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** P0)
    (pcFree_sepConj (by pcf) hP0) hbeq
  have hbeq' : cpsBranchWithin 1 (mulBase + 104) mulCR
      (((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) ** P)
      (mulBase + 232)
        (⌜byte = 0⌝ ** ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          ((.x5 : Reg) ↦ᵣ byte) ** P)
      (mulBase + 108)
        (⌜byte ≠ 0⌝ ** ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          ((.x5 : Reg) ↦ᵣ byte) ** P) := by
    refine cpsBranchWithin_weaken (fun _ hp => by
        dsimp [P, P0, outerLoopInv, outerStableNoX0] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        dsimp [P, P0, outerLoopInv, outerStableNoX0] at hq ⊢
        xperm_hyp hq)
      (fun _ hq => by
        dsimp [P, P0, outerLoopInv, outerStableNoX0] at hq ⊢
        xperm_hyp hq) hbeqF
  have hzero : cpsTripleWithin 104 (mulBase + 232) (mulBase + 84) mulCR
      (⌜byte = 0⌝ ** ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        ((.x5 : Reg) ↦ᵣ byte) ** P)
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr (i + 1)) := by
    refine cpsTripleWithin_pure_pre ?_
    intro hzero_eq
    have hstate : mulState aBytes b (i + 1) = mulState aBytes b i := by
      rw [mulState, mulOuterStep]
      have hgetD : aBytes.getD (31 - i) (0 : BitVec 8) =
          aBytes[31 - i]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
        rfl
      have hbyte8 : aBytes[31 - i]'(by omega) = (0 : BitVec 8) := by
        apply BitVec.eq_of_toNat_eq
        have hlt64 : (aBytes[31 - i]'(by omega)).toNat < 2 ^ 64 := by omega
        have hmod : (aBytes[31 - i]'(by omega)).toNat % 2 ^ 64 =
            (aBytes[31 - i]'(by omega)).toNat := Nat.mod_eq_of_lt hlt64
        have hbyte_toNat : byte.toNat =
            (aBytes[31 - i]'(by omega)).toNat % 2 ^ 64 := by
          dsimp [byte]
          simp only [BitVec.toNat_setWidth]
        have hmod0 := congrArg BitVec.toNat hzero_eq
        rw [hbyte_toNat, hmod] at hmod0
        exact hmod0
      rw [hgetD, hbyte8]
      rfl
    have hzero0 := outerNext_spec P hP i hi
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken
        (fun _ hp => by
          have hp' := sepConj_mono_right
            (sepConj_mono_left (regIs_to_regOwn .x5 byte)) _ hp
          xperm_hyp hp')
        (fun _ hq => by
          dsimp [outerHeaderInv, outerLoopInv, P] at hq ⊢
          rw [hstate] at ⊢
          xperm_hyp hq) hzero0)
  have hnonzero : cpsTripleWithin 104 (mulBase + 108) (mulBase + 84) mulCR
      (⌜byte ≠ 0⌝ ** ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        ((.x5 : Reg) ↦ᵣ byte) ** P)
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr (i + 1)) := by
    refine cpsTripleWithin_pure_pre ?_
    intro hneq
    have hnonzero0 := mulNonzero_spec F hF aBytes hlen
      spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i hi byte
      (by
        have hlt64 : (aBytes[31 - i]'(by omega)).toNat < 2 ^ 64 := by omega
        have hmod : (aBytes[31 - i]'(by omega)).toNat % 2 ^ 64 =
            (aBytes[31 - i]'(by omega)).toNat := Nat.mod_eq_of_lt hlt64
        have hbyte_toNat : byte.toNat =
            (aBytes[31 - i]'(by omega)).toNat % 2 ^ 64 := by
          dsimp [byte]
          simp only [BitVec.toNat_setWidth]
        rw [hbyte_toNat, hmod]
        exact (aBytes[31 - i]'(by omega)).isLt) hneq (by rfl)
      (byte.toNat * b.toNat) rfl
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp [P] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => hq) hnonzero0
  have hbranch := cpsBranchWithin_merge_same_cr (nSteps2 := 104)
    hbeq' hzero hnonzero
  have hseq := cpsTripleWithin_seq_same_cr hprefix' hbranch
  simpa only [Nat.add_assoc] using hseq

theorem outerLoop_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (aPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 3521 (mulBase + 84) (mulBase + 240) mulCR
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0)
      (outerHeaderInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 32) := by
  apply outerLoop_control_spec F hF aBytes
    spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 109
  intro i hi
  apply outerCycle_spec F hF aBytes hlen
    spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i hi halignA
  · omega
  · exact hvalidA (31 - i) (by omega)

/- private theorem outerHeaderInit_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes accBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr v5 v6 : Word)
    (hlen : accBytes.length = 40) :
    cpsTripleWithin 2 (mulBase + 76) (mulBase + 84) mulCR
      (F ** bytesRegion aPtr aBytes **
        ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
        ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x5 : Reg) ↦ᵣ accBase) **
        ((.x6 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
        regOwn .x7 ** regOwn .x13 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        frameSlots spNew vRa v8 v9 v18 v19 v20)
      (outerHeaderInv (F ** regOwn .x7 ** regOwn .x13 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr 0) := by
  have h20 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x20 v20 (0 : Word) (mulBase + 76) (by decide))
  rw [show mulBase + 76 + 4 = mulBase + 80 from by decide] at h20
  have h20F := cpsTripleWithin_frameR
    (F ** bytesRegion aPtr aBytes **
      ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
      ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x5 : Reg) ↦ᵣ accBase) ** ((.x6 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
      regOwn .x7 ** regOwn .x13 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by exact pcFree_sepConj hF (by pcf)) h20
  have h5 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x5 old5 (32 : Word) (mulBase + 80) (by decide))
  rw [show mulBase + 80 + 4 = mulBase + 84 from by decide] at h5
  have h5F := cpsTripleWithin_frameR
    (F ** bytesRegion aPtr aBytes **
      ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
      ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
      ((.x20 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x6 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
      regOwn .x7 ** regOwn .x13 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 **
      frameSlots spNew vRa v8 v9 v18 v19 v20)
    (by exact pcFree_sepConj hF (by pcf)) h5
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h20F h5F
  refine cpsTripleWithin_weaken
    (fun _ hp => by dsimp [outerHeaderInitPre]; xperm_hyp hp)
    (fun _ hq => ?_) hseq
  dsimp [outerHeaderInv, outerLoopInv] at hq ⊢
  simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq -/


end EvmAsm.Codegen.U256MulU64Be
