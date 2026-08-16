import EvmAsm.Codegen.Programs.U256MulU64Be.WholeModel

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm Rv64.SAsm.Stmt

def rippleInv
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m : Nat) (k : Nat) : Assertion :=
  rippleFrame F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m k **
    regOwn .x31

def outerStableNoX0
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word) : Assertion :=
  F ** bytesRegion aPtr aBytes **
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
    ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
    ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ b) **
    ((.x12 : Reg) ↦ᵣ outPtr) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

def rippleLoopInv
    (F : Assertion) (aBytes : List (BitVec 8))
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m k : Nat) : Assertion :=
  outerStableNoX0 F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
    ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
    ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 ((m % 2 ^ 64) / 256 ^ k)) **
    ((.x28 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (i + k))) **
    ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64
      (mulCarry (mulState aBytes b i) (m % 2 ^ 64) i k)) **
    regOwn .x13 ** regOwn .x31 **
    bytesRegion accBase (rippleState (mulState aBytes b i) (m % 2 ^ 64) i k)

theorem ripple_x6_shift (m k : Nat) (_hk : k < 8) :
    (BitVec.ofNat 64 ((m % 2 ^ 64) / 256 ^ k) >>> 8).toNat =
      (m % 2 ^ 64) / 256 ^ (k + 1) := by
  rw [toNat_shiftRight_8, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by
      have hm := Nat.mod_lt m (by decide : 0 < 2 ^ 64)
      have hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hm),
    Nat.div_div_eq_div_mul]
  congr 1

theorem word_and255_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n &&& (BitVec.ofNat 64 255)) =
      BitVec.ofNat 64 (n % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, show (BitVec.ofNat 64 255).toNat = 255 from by decide,
    show (255 : Nat) = 2 ^ 8 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_ofNat]
  omega

theorem word_and255_word (x : Word) :
    (x &&& BitVec.ofNat 64 255) = BitVec.ofNat 64 (x.toNat % 256) := by
  have hx : x = BitVec.ofNat 64 x.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  rw [hx]
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt] using
    (word_and255_ofNat x.toNat x.isLt)

theorem word_add3_toNat (a b c : Nat) (h : a + b + c < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b + BitVec.ofNat 64 c).toNat =
      a + b + c := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a + b < 2 ^ 64),
    Nat.mod_eq_of_lt h]

theorem word_add3_shift8 (a b : Nat) (c : Nat)
    (ha : a < 256) (hb : b < 256) (hc : c ≤ 1) :
    ((BitVec.ofNat 64 a) + BitVec.ofNat 64 b + BitVec.ofNat 64 c) >>> 8 =
      BitVec.ofNat 64 ((a + b + c) / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a + b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a + b + c < 2 ^ 64),
    BitVec.toNat_ofNat]
  omega

theorem rippleLbu_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (_hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m k : Nat) (hi : i < 32) (hk : k < 8) :
    cpsTripleWithin 1 (mulBase + 128) (mulBase + 132) mulCR
      (rippleInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m k)
      (rippleFrame F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m k **
        ((.x31 : Reg) ↦ᵣ
          (((rippleState (mulState aBytes b i) (m % 2 ^ 64) i k).getD
            (i + k) 0).zeroExtend 64))) := by
  let accE := mulState aBytes b i
  let accK := rippleState accE (m % 2 ^ 64) i k
  let ptr := accBase + BitVec.ofNat 64 (i + k)
  let Q : Assertion :=
    outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 ((m % 2 ^ 64) / 256 ^ k)) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64)) **
      ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64
        (mulCarry accE (m % 2 ^ 64) i k)) ** regOwn .x13
  have hstep_len : ∀ (xs : List (BitVec 8)) (j : Nat),
      (mulOuterStep aBytes b xs j).length = xs.length := by
    intro xs j
    dsimp [mulOuterStep]
    split
    · rfl
    · rw [List.length_set, length_rippleState]
  have hstate_len : ∀ j : Nat, (mulState aBytes b j).length = 40 := by
    intro j
    induction j with
    | zero => simp [mulState]
    | succ j ih =>
        rw [mulState, hstep_len, ih]
  have hacc : accE.length = 40 := by
    simpa [accE] using hstate_len i
  have hiacc : i + k < accE.length := by
    rw [hacc]
    omega
  have hvalid := accBase_valid_byte (i + k) (by rw [hacc] at hiacc; exact hiacc)
  have hover := accBase_no_overflow (i + k) (by rw [hacc] at hiacc; exact hiacc)
  have hQ : Q.pcFree := by
    dsimp [Q, outerStableNoAcc]
    apply pcFree_sepConj
    · apply pcFree_sepConj
      · exact hF
      · pcf
    · pcf
  have hiacc' : i + k < accK.length := by
    simpa [accK, length_rippleState] using hiacc
  have hown0 : cpsTripleWithin 1 (mulBase + 128) (mulBase + 132) mulCR
      ((Q ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK) ** regOwn .x31)
      (Q ** ((.x28 : Reg) ↦ᵣ ptr) **
        ((.x31 : Reg) ↦ᵣ (accK.getD (i + k) 0).zeroExtend 64) **
        bytesRegion accBase accK) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x31) (P := Q ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK) ?_
    intro old31
    have hlbu := bytesRegion_lbu_within .x31 .x28 accBase old31
      (mulBase + 128) accK (i + k) (by decide)
      accBase_align hiacc' hover hvalid
    have hlbu' := cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := by code_mem) hlbu
    have hfr := cpsTripleWithin_frameR Q hQ hlbu'
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun _ hq => by
        have hget : accK.getD (i + k) 0 = accK[i + k]'hiacc' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiacc']
          rfl
        rw [hget]
        xperm_hyp hq) hfr
  have hown : cpsTripleWithin 1 (mulBase + 128) (mulBase + 132) mulCR
      (Q ** ((.x28 : Reg) ↦ᵣ ptr) ** bytesRegion accBase accK ** regOwn .x31)
      (Q ** ((.x28 : Reg) ↦ᵣ ptr) **
        ((.x31 : Reg) ↦ᵣ (accK.getD (i + k) 0).zeroExtend 64) **
        bytesRegion accBase accK) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun _ hq => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq) hown0
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hown
  · dsimp [rippleInv, rippleFrame, rippleBase, Q, outerStableNoAcc,
      accK, accE, ptr] at hp ⊢
    xperm_hyp hp
  · dsimp [rippleFrame, rippleBase, Q, outerStableNoAcc, accK, accE, ptr] at hq ⊢
    xperm_hyp hq

theorem rippleBody_exact
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (_hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m k : Nat)
    (hi : i < 32) (hk : k < 8) (old13 old31 : Word) :
    cpsTripleWithin 10 (mulBase + 128) (mulBase + 168) mulCR
      (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m k ** ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ old31))
      (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m (k + 1) **
        ((.x13 : Reg) ↦ᵣ
          BitVec.ofNat 64
            ((m % 2 ^ 64 / 256 ^ k +
              ((rippleState (mulState aBytes b i) (m % 2 ^ 64) i k).getD
                (i + k) 0).toNat +
              mulCarry (mulState aBytes b i) (m % 2 ^ 64) i k) % 256)) **
        ((.x31 : Reg) ↦ᵣ
          ((rippleState (mulState aBytes b i) (m % 2 ^ 64) i k).getD
            (i + k) 0).zeroExtend 64 +
            BitVec.ofNat 64
              (m % 2 ^ 64 / 256 ^ k % 256) +
            BitVec.ofNat 64
              (mulCarry (mulState aBytes b i) (m % 2 ^ 64) i k))) := by
  let accE := mulState aBytes b i
  let M0 := m % 2 ^ 64
  let accK := rippleState accE M0 i k
  let ptr := accBase + BitVec.ofNat 64 (i + k)
  let oldNat := (accK.getD (i + k) 0).toNat
  let lowNat := M0 / 256 ^ k % 256
  let carryNat := mulCarry accE M0 i k
  let totalNat := oldNat + lowNat + carryNat
  let oldW := (accK.getD (i + k) 0).zeroExtend 64
  let lowW := BitVec.ofNat 64 lowNat
  let carryW := BitVec.ofNat 64 carryNat
  let sum1W := oldW + lowW
  let sumW := sum1W + carryW
  let newW := BitVec.ofNat 64 (totalNat % 256)
  let H : Assertion :=
    outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64))
  have hstep_len : ∀ (xs : List (BitVec 8)) (j : Nat),
      (mulOuterStep aBytes b xs j).length = xs.length := by
    intro xs j
    dsimp [mulOuterStep]
    split
    · rfl
    · rw [List.length_set, length_rippleState]
  have hacc : accE.length = 40 := by
    have hs : ∀ j : Nat, (mulState aBytes b j).length = 40 := by
      intro j
      induction j with
      | zero => simp [mulState]
      | succ j ih => rw [mulState, hstep_len, ih]
    simpa [accE] using hs i
  have hiacc : i + k < accE.length := by
    rw [hacc]
    omega
  have hiaccK : i + k < accK.length := by
    simpa [accK, length_rippleState] using hiacc
  have hi40 : i + k < 40 := by simpa [hacc] using hiacc
  have hptr_valid := accBase_valid_byte (i + k) hi40
  have hptr_over := accBase_no_overflow (i + k) hi40
  have hget : accK.getD (i + k) 0 = accE.getD (i + k) 0 := by
    exact getD_rippleState_of_ge accE M0 i k (i + k) (by omega)
  have holdElem : accK.getD (i + k) 0 = accK[i + k]'hiaccK := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiaccK]
    rfl
  have hcarryNext : mulCarry accE M0 i (k + 1) = totalNat / 256 := by
    rw [show mulCarry accE M0 i (k + 1) =
      ((accE.getD (i + k) 0).toNat + M0 / 256 ^ k % 256 + carryNat) / 256 from rfl]
    rw [← hget]
  have hlow_bound : M0 / 256 ^ k < 2 ^ 64 := by
    have hm := Nat.mod_lt m (by decide : 0 < 2 ^ 64)
    dsimp [M0]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hm
  have hmask_low :
      (BitVec.ofNat 64 (M0 / 256 ^ k) &&& BitVec.ofNat 64 255) = lowW := by
    dsimp [lowW, lowNat]
    rw [word_and255_ofNat (M0 / 256 ^ k) hlow_bound]
  have hsum_nat : sumW.toNat = totalNat := by
    have hold_lt : oldNat < 256 := by
      have := (accK.getD (i + k) (0 : BitVec 8)).isLt
      omega
    have hlow_lt : lowNat < 256 := Nat.mod_lt _ (by decide)
    have hcarry_le : carryNat ≤ 1 := mulCarry_le_one accE M0 i k
    have htotal : oldNat + lowNat + carryNat < 2 ^ 64 := by omega
    have holdW : oldW = BitVec.ofNat 64 oldNat := by
      apply BitVec.eq_of_toNat_eq
      dsimp [oldW, oldNat]
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    dsimp [sumW, sum1W]
    rw [holdW]
    exact word_add3_toNat oldNat lowNat carryNat htotal
  have hmask_sum : sumW &&& BitVec.ofNat 64 255 = newW := by
    rw [word_and255_word, hsum_nat]
  have hmask_sum' : sumW &&& (255 : Word) = newW := by
    exact hmask_sum
  have hshift_sum : sumW >>> 8 = BitVec.ofNat 64 (totalNat / 256) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      hsum_nat, BitVec.toNat_ofNat]
    rw [show 2 ^ 8 = 256 by decide,
      Nat.mod_eq_of_lt (by have := sumW.isLt; omega)]
  have hshift_sum' : sumW >>> (BitVec.ofNat 6 8).toNat =
      BitVec.ofNat 64 (totalNat / 256) := by
    simpa using hshift_sum
  have hshift_low :
      (BitVec.ofNat 64 (M0 / 256 ^ k) >>> 8) =
        BitVec.ofNat 64 (M0 / 256 ^ (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hm0 : M0 < 2 ^ 64 := by
      dsimp [M0]
      exact Nat.mod_lt _ (by decide)
    have hk0 : M0 / 256 ^ k < 2 ^ 64 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hm0
    have hk1 : M0 / 256 ^ (k + 1) < 2 ^ 64 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hm0
    rw [Nat.mod_eq_of_lt hk0, Nat.mod_eq_of_lt hk1,
      show 2 ^ 8 = 256 by decide, Nat.div_div_eq_div_mul]
    congr 1
  have hptr_succ : ptr + Rv64.signExtend12 (1 : BitVec 12) =
      accBase + BitVec.ofNat 64 (i + (k + 1)) := by
    dsimp [ptr]
    exact accCursor1_succ i k (by omega)
  have hctr_succ :
      BitVec.ofNat 64 (8 - k) + Rv64.signExtend12 (-1 : BitVec 12) =
        BitVec.ofNat 64 (8 - (k + 1)) := rippleCtr_dec k hk
  have hsb_state :
      (accK.set (i + k) (newW.truncate 8)) =
        rippleState accE M0 i (k + 1) := by
    have hvalue : newW.truncate 8 =
        BitVec.ofNat 8
          ((accE.getD (i + k) 0).toNat + M0 / 256 ^ k % 256 + carryNat) := by
      have hget8 : accK.getD (i + k) (0 : BitVec 8) =
          accE.getD (i + k) (0 : BitVec 8) := hget
      have hgetNat := congrArg BitVec.toNat hget8
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      dsimp [newW, totalNat, oldNat, lowNat]
      change
        ((accK.getD (i + k) (0 : BitVec 8)).toNat + M0 / 256 ^ k % 256 + carryNat) % 256
            % 2 ^ 64 % 256 =
          (BitVec.ofNat 8
            ((accE.getD (i + k) (0 : BitVec 8)).toNat + M0 / 256 ^ k % 256 + carryNat)).toNat
      rw [hgetNat]
      simp [BitVec.toNat_ofNat]
    rw [rippleState_succ, hvalue]
  let lowCur := BitVec.ofNat 64 (M0 / 256 ^ k)
  let lowNext := BitVec.ofNat 64 (M0 / 256 ^ (k + 1))
  let rem := BitVec.ofNat 64 (8 - k)
  let remNext := BitVec.ofNat 64 (8 - (k + 1))
  let carryW := BitVec.ofNat 64 carryNat
  let carryNextW := BitVec.ofNat 64 (totalNat / 256)
  let nextPtr := accBase + BitVec.ofNat 64 (i + (k + 1))
  let nextAcc := accK.set (i + k) (newW.truncate 8)
  have hshift_low' : lowCur >>> 8 = lowNext := by
    dsimp [lowCur, lowNext]
    exact hshift_low
  let S : Assertion :=
    outerStableNoAcc F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr **
      ((.x20 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x5 : Reg) ↦ᵣ byte) **
      ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 (m / 2 ^ 64))
  let B0 : Assertion :=
    S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryW) **
      bytesRegion accBase accK
  let Bmem : Assertion :=
    S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryW) **
      bytesRegion accBase nextAcc
  let Bmem30 : Assertion :=
    S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryNextW) **
      bytesRegion accBase nextAcc
  let Bmem306 : Assertion :=
    S ** ((.x6 : Reg) ↦ᵣ lowNext) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryNextW) **
      bytesRegion accBase nextAcc
  let Bmem306p : Assertion :=
    S ** ((.x6 : Reg) ↦ᵣ lowNext) ** ((.x28 : Reg) ↦ᵣ nextPtr) **
      ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryNextW) **
      bytesRegion accBase nextAcc
  let B1 : Assertion :=
    S ** ((.x6 : Reg) ↦ᵣ lowNext) ** ((.x28 : Reg) ↦ᵣ nextPtr) **
      ((.x29 : Reg) ↦ᵣ remNext) ** ((.x30 : Reg) ↦ᵣ carryNextW) **
      bytesRegion accBase nextAcc
  have hS : S.pcFree := by
    dsimp [S, outerStableNoAcc]
    apply pcFree_sepConj
    · apply pcFree_sepConj
      · exact hF
      · pcf
    · pcf
  have hR0 :
      (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x29 : Reg) ↦ᵣ rem) **
        ((.x30 : Reg) ↦ᵣ carryW) ** ((.x13 : Reg) ↦ᵣ old13)).pcFree := by
    exact pcFree_sepConj hS (by pcFree)
  have hR1 :
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** ((.x29 : Reg) ↦ᵣ rem) **
        ((.x30 : Reg) ↦ᵣ carryW) ** bytesRegion accBase accK **
        ((.x31 : Reg) ↦ᵣ oldW)).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h0raw := bytesRegion_lbu_within .x31 .x28 accBase old31
    (mulBase + 128) accK (i + k) (by decide) accBase_align hiaccK hptr_over hptr_valid
  rw [show (mulBase + 128 : Word) + 4 = mulBase + 132 from by decide] at h0raw
  have h0e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h0raw
  have h0f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x29 : Reg) ↦ᵣ rem) **
      ((.x30 : Reg) ↦ᵣ carryW) ** ((.x13 : Reg) ↦ᵣ old13)) hR0 h0e
  have holdW : oldW = (accK[i + k]'hiaccK).zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    dsimp [oldW]
    simp only [BitVec.toNat_setWidth]
    have hemod := congrArg (fun n : Nat => n % 2 ^ 64)
      (congrArg BitVec.toNat holdElem)
    exact hemod
  rw [← holdW] at h0f
  have h0 : cpsTripleWithin 1 (mulBase + 128) (mulBase + 132) mulCR
      (B0 ** ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ old31))
      (B0 ** ((.x13 : Reg) ↦ᵣ old13) **
        ((.x31 : Reg) ↦ᵣ oldW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0f
  have h1raw := andi_spec_gen_within .x13 .x6 old13 lowCur
    (255 : BitVec 12) (mulBase + 132) (by decide)
  rw [show (mulBase + 132 : Word) + 4 = mulBase + 136 from by decide,
    show Rv64.signExtend12 (255 : BitVec 12) = (255 : Word) from by decide] at h1raw
  dsimp [lowCur] at h1raw
  rw [hmask_low] at h1raw
  have h1e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h1raw
  have h1f := cpsTripleWithin_frameR
    (S ** ((.x28 : Reg) ↦ᵣ ptr) ** ((.x29 : Reg) ↦ᵣ rem) **
      ((.x30 : Reg) ↦ᵣ carryW) ** bytesRegion accBase accK **
      ((.x31 : Reg) ↦ᵣ oldW)) hR1 h1e
  have h1 : cpsTripleWithin 1 (mulBase + 132) (mulBase + 136) mulCR
      ((B0 ** ((.x13 : Reg) ↦ᵣ old13)) **
        ((.x31 : Reg) ↦ᵣ oldW))
      ((B0 ** ((.x13 : Reg) ↦ᵣ lowW)) **
        ((.x31 : Reg) ↦ᵣ oldW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1f
  have hR2 :
      (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
        ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryW) **
        bytesRegion accBase accK).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h2raw := add_spec_gen_rd_eq_rs1_within .x31 .x13 oldW lowW
    (mulBase + 136) (by decide)
  rw [show (mulBase + 136 : Word) + 4 = mulBase + 140 from by decide] at h2raw
  have h2e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h2raw
  have h2f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryW) **
      bytesRegion accBase accK) hR2 h2e
  have h2 : cpsTripleWithin 1 (mulBase + 136) (mulBase + 140) mulCR
      (B0 ** ((.x13 : Reg) ↦ᵣ lowW) ** ((.x31 : Reg) ↦ᵣ oldW))
      (B0 ** ((.x13 : Reg) ↦ᵣ lowW) ** ((.x31 : Reg) ↦ᵣ sum1W)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2f
  have hR3 :
      (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
        ((.x29 : Reg) ↦ᵣ rem) ** bytesRegion accBase accK **
        ((.x13 : Reg) ↦ᵣ lowW)).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h3raw := add_spec_gen_rd_eq_rs1_within .x31 .x30 sum1W carryW
    (mulBase + 140) (by decide)
  rw [show (mulBase + 140 : Word) + 4 = mulBase + 144 from by decide] at h3raw
  have h3e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h3raw
  have h3f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** bytesRegion accBase accK **
      ((.x13 : Reg) ↦ᵣ lowW)) hR3 h3e
  have h3 : cpsTripleWithin 1 (mulBase + 140) (mulBase + 144) mulCR
      (B0 ** ((.x13 : Reg) ↦ᵣ lowW) ** ((.x31 : Reg) ↦ᵣ sum1W))
      (B0 ** ((.x13 : Reg) ↦ᵣ lowW) ** ((.x31 : Reg) ↦ᵣ sumW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h3f
  have hR4 :
      (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
        ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryW) **
        bytesRegion accBase accK).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h4raw := andi_spec_gen_within .x13 .x31 lowW sumW
    (255 : BitVec 12) (mulBase + 144) (by decide)
  rw [show (mulBase + 144 : Word) + 4 = mulBase + 148 from by decide,
    show Rv64.signExtend12 (255 : BitVec 12) = (255 : Word) from by decide] at h4raw
  have h4e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h4raw
  have h4f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** ((.x30 : Reg) ↦ᵣ carryW) **
      bytesRegion accBase accK) hR4 h4e
  have h4 : cpsTripleWithin 1 (mulBase + 144) (mulBase + 148) mulCR
      (B0 ** ((.x13 : Reg) ↦ᵣ lowW) ** ((.x31 : Reg) ↦ᵣ sumW))
      (B0 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        rw [hmask_sum'] at hq
        xperm_hyp hq) h4f
  have h5raw := bytesRegion_sb_within .x28 .x13 accBase newW
    (mulBase + 148) accK (i + k) accBase_align hiaccK hptr_over hptr_valid
  rw [show (mulBase + 148 : Word) + 4 = mulBase + 152 from by decide] at h5raw
  have h5e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h5raw
  rw [hsb_state] at h5e
  have hR5 :
      (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x29 : Reg) ↦ᵣ rem) **
        ((.x30 : Reg) ↦ᵣ carryW) ** ((.x31 : Reg) ↦ᵣ sumW)).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h5f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x29 : Reg) ↦ᵣ rem) **
      ((.x30 : Reg) ↦ᵣ carryW) ** ((.x31 : Reg) ↦ᵣ sumW)) hR5 h5e
  have h5 : cpsTripleWithin 1 (mulBase + 148) (mulBase + 152) mulCR
      (B0 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW))
      (Bmem ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        rw [← hsb_state] at hq
        xperm_hyp hq) h5f
  have h6raw := srli_spec_gen_within .x30 .x31 carryW sumW
    (8 : BitVec 6) (mulBase + 152) (by decide)
  rw [show (mulBase + 152 : Word) + 4 = mulBase + 156 from by decide] at h6raw
  change cpsTripleWithin 1 _ _ _ _
    (((.x31 : Reg) ↦ᵣ sumW) ** ((.x30 : Reg) ↦ᵣ (sumW >>> 8))) at h6raw
  rw [hshift_sum] at h6raw
  have h6e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h6raw
  have hR6 :
      (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
        ((.x29 : Reg) ↦ᵣ rem) ** bytesRegion accBase nextAcc **
        ((.x13 : Reg) ↦ᵣ newW)).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h6f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowCur) ** ((.x28 : Reg) ↦ᵣ ptr) **
      ((.x29 : Reg) ↦ᵣ rem) ** bytesRegion accBase nextAcc **
      ((.x13 : Reg) ↦ᵣ newW)) hR6 h6e
  have h6 : cpsTripleWithin 1 (mulBase + 152) (mulBase + 156) mulCR
      (Bmem ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW))
      (Bmem30 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h6f
  have h7raw := srli_spec_gen_same_within .x6 lowCur
    (8 : BitVec 6) (mulBase + 156) (by decide)
  rw [show (mulBase + 156 : Word) + 4 = mulBase + 160 from by decide] at h7raw
  change cpsTripleWithin 1 _ _ _ _
    (((.x6 : Reg) ↦ᵣ (lowCur >>> 8))) at h7raw
  rw [hshift_low'] at h7raw
  have h7e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h7raw
  have hR7 :
      (S ** ((.x28 : Reg) ↦ᵣ ptr) ** ((.x29 : Reg) ↦ᵣ rem) **
        ((.x30 : Reg) ↦ᵣ carryNextW) ** bytesRegion accBase nextAcc **
        ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h7f := cpsTripleWithin_frameR
    (S ** ((.x28 : Reg) ↦ᵣ ptr) ** ((.x29 : Reg) ↦ᵣ rem) **
      ((.x30 : Reg) ↦ᵣ carryNextW) ** bytesRegion accBase nextAcc **
      ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) hR7 h7e
  have h7 : cpsTripleWithin 1 (mulBase + 156) (mulBase + 160) mulCR
      (Bmem30 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW))
      (Bmem306 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h7f
  have h8raw := addi_spec_gen_same_within .x28 ptr
    (1 : BitVec 12) (mulBase + 160) (by decide)
  rw [show (mulBase + 160 : Word) + 4 = mulBase + 164 from by decide,
    hptr_succ] at h8raw
  have h8e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h8raw
  have hR8 :
      (S ** ((.x6 : Reg) ↦ᵣ lowNext) ** ((.x29 : Reg) ↦ᵣ rem) **
        ((.x30 : Reg) ↦ᵣ carryNextW) ** bytesRegion accBase nextAcc **
        ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h8f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowNext) ** ((.x29 : Reg) ↦ᵣ rem) **
      ((.x30 : Reg) ↦ᵣ carryNextW) ** bytesRegion accBase nextAcc **
      ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) hR8 h8e
  have h8 : cpsTripleWithin 1 (mulBase + 160) (mulBase + 164) mulCR
      (Bmem306 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW))
      (Bmem306p ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h8f
  have h9raw := addi_spec_gen_same_within .x29 rem
    (-1 : BitVec 12) (mulBase + 164) (by decide)
  rw [show (mulBase + 164 : Word) + 4 = mulBase + 168 from by decide,
    hctr_succ] at h9raw
  have h9e := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem) h9raw
  have hR9 :
      (S ** ((.x6 : Reg) ↦ᵣ lowNext) ** ((.x28 : Reg) ↦ᵣ nextPtr) **
        ((.x30 : Reg) ↦ᵣ carryNextW) ** bytesRegion accBase nextAcc **
        ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)).pcFree := by
    exact pcFree_sepConj hS (by pcf)
  have h9f := cpsTripleWithin_frameR
    (S ** ((.x6 : Reg) ↦ᵣ lowNext) ** ((.x28 : Reg) ↦ᵣ nextPtr) **
      ((.x30 : Reg) ↦ᵣ carryNextW) ** bytesRegion accBase nextAcc **
      ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) hR9 h9e
  have h9 : cpsTripleWithin 1 (mulBase + 164) (mulBase + 168) mulCR
      (Bmem306p ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW))
      (B1 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h9f
  have hsumW_explicit : sumW = sum1W + BitVec.ofNat 64 carryNat := by
    rfl
  have hcarryNext' :
      mulCarry (mulState aBytes b i) (m % 2 ^ 64) i (k + 1) = totalNat / 256 := by
    simpa [accE, M0] using hcarryNext
  suffices hbody : cpsTripleWithin 10 (mulBase + 128) (mulBase + 168) mulCR
      (B0 ** ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ old31))
      (B1 ** ((.x13 : Reg) ↦ᵣ newW) ** ((.x31 : Reg) ↦ᵣ sumW)) by
    simp only [rippleBase]
    rw [hcarryNext']
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hbody
    · dsimp [B0, S, outerStableNoAcc, accK, accE, ptr, lowCur, rem,
        carryW, carryNat, oldW, M0] at hp ⊢
      xperm_hyp hp
    · simp [B1, S, outerStableNoAcc, accK, accE, lowNext, remNext,
        nextPtr, nextAcc, carryNextW, oldW, lowW, sum1W, hsumW_explicit,
        newW, oldNat, lowNat, totalNat, carryNat, hsb_state,
        M0, Nat.add_comm, Nat.add_left_comm] at hq ⊢
      xperm_hyp hq
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem rippleBody_owned_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (_hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m k : Nat)
    (hi : i < 32) (hk : k < 8) :
    cpsTripleWithin 10 (mulBase + 128) (mulBase + 168) mulCR
      (rippleInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m k)
      (rippleInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
        i byte m (k + 1)) := by
  have hconcrete : ∀ old13 old31,
      cpsTripleWithin 10 (mulBase + 128) (mulBase + 168) mulCR
        (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m k ** ((.x13 : Reg) ↦ᵣ old13) ** ((.x31 : Reg) ↦ᵣ old31))
        (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m (k + 1) ** regOwn .x13 ** regOwn .x31) := by
    intro old13 old31
    have hraw := rippleBody_exact F hF aBytes _hlen
      spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m k hi hk old13 old31
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) hraw
    let new13 : Word :=
      BitVec.ofNat 64
        ((m % 2 ^ 64 / 256 ^ k +
          ((rippleState (mulState aBytes b i) (m % 2 ^ 64) i k).getD
            (i + k) 0).toNat +
          mulCarry (mulState aBytes b i) (m % 2 ^ 64) i k) % 256)
    let new31 : Word :=
      (((rippleState (mulState aBytes b i) (m % 2 ^ 64) i k).getD
        (i + k) 0).zeroExtend 64) +
      BitVec.ofNat 64 (m % 2 ^ 64 / 256 ^ k % 256) +
      BitVec.ofNat 64
        (mulCarry (mulState aBytes b i) (m % 2 ^ 64) i k)
    have hq0 :
        (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m (k + 1) **
          (((.x13 : Reg) ↦ᵣ new13) ** ((.x31 : Reg) ↦ᵣ new31))) s := by
      simpa [new13, new31, sepConj_assoc'] using hq
    have hq' :
        (rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m (k + 1) ** regOwn .x13 ** regOwn .x31) s := by
      have hq'' := sepConj_mono
        (P := rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m (k + 1))
        (P' := rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m (k + 1))
        (Q := ((.x13 : Reg) ↦ᵣ new13) ** ((.x31 : Reg) ↦ᵣ new31))
        (Q' := regOwn .x13 ** regOwn .x31)
        (fun _ h => h)
        (sepConj_mono (regIs_to_regOwn .x13 new13)
          (regIs_to_regOwn .x31 new31)) s hq0
      simpa only [sepConj_assoc'] using hq''
    exact hq'
  have hown := cpsTripleWithin_of_forall_regIs_to_regOwn2
    (r1 := .x13) (r2 := .x31)
    (P := rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
      i byte m k)
    (Q := rippleBase F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
      i byte m (k + 1) ** regOwn .x13 ** regOwn .x31)
    hconcrete
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hown
  · dsimp [rippleInv, rippleFrame] at hp ⊢
    xperm_hyp hp
  · dsimp [rippleInv, rippleFrame] at hq ⊢
    xperm_hyp hq

theorem rippleLoop_guard_mem :
    ∀ a i,
      CodeReq.singleton (mulBase + 168)
          (.BNE .x29 .x0 (-40 : BitVec 13)) a = some i →
        mulCR a = some i := by
  intro a i h
  exact CodeReq.ofProg_mem_at mulBase (mulBase + 168) mulProg 42
    (.BNE .x29 .x0 (-40 : BitVec 13)) (by decide) (by decide) (by decide)
    (by decide) a i h

theorem rippleLoop_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes : List (BitVec 8)) (_hlen : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (i : Nat) (byte : Word) (m : Nat) (hi : i < 32) :
    cpsTripleWithin 88 (mulBase + 128) (mulBase + 172) mulCR
      (((.x29 : Reg) ↦ᵣ (8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m 0)
      (((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          i byte m 8) := by
  let inv : Nat → Assertion := fun n =>
    rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
      i byte m (8 - n)
  have hinv : ∀ n, (inv n).pcFree := by
    intro n
    dsimp [inv, rippleLoopInv, outerStableNoX0]
    apply pcFree_sepConj
    · apply pcFree_sepConj
      · exact hF
      · pcf
    · pcf
  have hbody : ∀ n, n < 8 →
      cpsTripleWithin 10 (mulBase + 128) (mulBase + 168) mulCR
        (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** inv (n + 1))
        (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** inv n) := by
    intro n hn
    have hk : 7 - n < 8 := by omega
    have hraw := rippleBody_owned_spec F hF aBytes _hlen
      spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr i byte m (7 - n) hi hk
    have hconv : cpsTripleWithin 10 (mulBase + 128) (mulBase + 168) mulCR
        (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - (7 - n))) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
            i byte m (7 - n))
        (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - (7 - n + 1))) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          rippleLoopInv F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
            i byte m (7 - n + 1)) := by
      refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hraw
      · dsimp [rippleInv, rippleFrame, rippleBase, outerStableNoAcc,
          rippleLoopInv, outerStableNoX0] at hp ⊢
        xperm_hyp hp
      · dsimp [rippleInv, rippleFrame, rippleBase, outerStableNoAcc,
          rippleLoopInv, outerStableNoX0] at hq ⊢
        xperm_hyp hq
    have hn1 : 8 - (n + 1) = 7 - n := by omega
    have hk1 : 7 - n + 1 = 8 - n := by omega
    have hpre : 8 - (7 - n) = n + 1 := by omega
    have hpost : 8 - (7 - n + 1) = n := by omega
    have hpost' : 8 - (8 - n) = n := by omega
    simpa [inv, hn1, hk1, hpre, hpost, hpost'] using hconv
  have hloop := countdownLoopBottom_spec mulCR (mulBase + 128) (mulBase + 168)
    .x29 (-40 : BitVec 13) 10 8 inv (by decide) (by decide) (by decide)
    (by
      rw [show Rv64.signExtend13 (-40 : BitVec 13) = (-40 : Word) from by decide]
      bv_omega)
    hinv rippleLoop_guard_mem hbody
  simpa [inv] using hloop


end EvmAsm.Codegen.U256MulU64Be
