/-
  EvmAsm.SLHDSA.VerifyProof

  Functional correctness of the RV64 SLH-DSA verifier `slhVerifyFn`
  (EvmAsm/SLHDSA/VerifySAsm.lean).

  The proof factors through the word-level reference verifier
  `SLHDSA.Demo.demoVerifyWords`:

  * §"Branch-free intermediate values" / `demoVerifyWords_eq` rewrite
    `demoVerifyWords` into a branch-free root comparison (all four FORS/XMSS
    parity `if`s collapse because the demo hashes are additive, so `hW` is
    symmetric in its two message blocks).
  * §"Block effects" prove, one register at a time, that each SAsm block
    (`load`, `wsetup`, `wots`, `final`) computes exactly the corresponding
    `demoVerifyWords` intermediate — culminating in `final_effect`, whose `a0`
    output is `1` iff `demoVerifyWords` accepts.
  * `slhVerifyFn_spec` assembles these via `vcgen`: the three load blocks'
    memory VCs (all dword loads land aligned in the input arena) and the
    strongest-postcondition VC, giving the full bounded CPS triple `Fn.Spec`.
  * `slhVerifyFn_post_fips` (capstone) rewrites the postcondition, at the
    packed message word, into the ported FIPS 205 result
    `SLHDSA.slhVerifyInternal` via `Demo.demoVerifyWords_correct`
    (EvmAsm/SLHDSA/DemoCorrect.lean).

  Every theorem here is kernel-checked and depends only on the three classical
  axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no
  `native_decide`/`bv_decide`.
-/

import EvmAsm.SLHDSA.VerifySAsm

namespace EvmAsm.Rv64
namespace SlhVerify
open SAsm SLHDSA SLHDSA.Demo Stmt

/-- Region of the verifier. -/
abbrev regionOf (pkSeed pkRoot msgW : Word) (s : SigWords) : Region :=
  ⟨inputBase, wordsBytes (inputWords pkSeed pkRoot msgW s)⟩

/-! ## Branch-free intermediate values (demoVerifyWords with the four `if`s collapsed). -/

variable (pkSeed pkRoot msgW : Word) (s : SigWords)

def hmV : Word := hmsgW s.r pkSeed pkRoot msgW
def idxLeafV : Word := hmV pkSeed pkRoot msgW s &&& 1
def f0V : Word := (hmV pkSeed pkRoot msgW s >>> 15) &&& 1
def f1V : Word := (hmV pkSeed pkRoot msgW s >>> 14) &&& 1
def leaf0V : Word := fW pkSeed (adrsW 3 (idxLeafV pkSeed pkRoot msgW s) 0 (f0V pkSeed pkRoot msgW s)) s.s0
def root0V : Word := hW pkSeed (adrsW 3 (idxLeafV pkSeed pkRoot msgW s) 1 0) (leaf0V pkSeed pkRoot msgW s) s.a0
def leaf1V : Word := fW pkSeed (adrsW 3 (idxLeafV pkSeed pkRoot msgW s) 0 (2 + f1V pkSeed pkRoot msgW s)) s.s1
def root1V : Word := hW pkSeed (adrsW 3 (idxLeafV pkSeed pkRoot msgW s) 1 1) (leaf1V pkSeed pkRoot msgW s) s.a1
def forsPkV : Word := mix (mix (tlInit pkSeed (adrsW 4 (idxLeafV pkSeed pkRoot msgW s) 0 0))
  (root0V pkSeed pkRoot msgW s)) (root1V pkSeed pkRoot msgW s)
def mbV : Word := forsPkV pkSeed pkRoot msgW s &&& 255
def dsumV : Word :=
  ((mbV pkSeed pkRoot msgW s >>> 7) &&& 1) + ((mbV pkSeed pkRoot msgW s >>> 6) &&& 1)
    + ((mbV pkSeed pkRoot msgW s >>> 5) &&& 1) + ((mbV pkSeed pkRoot msgW s >>> 4) &&& 1)
    + ((mbV pkSeed pkRoot msgW s >>> 3) &&& 1) + ((mbV pkSeed pkRoot msgW s >>> 2) &&& 1)
    + ((mbV pkSeed pkRoot msgW s >>> 1) &&& 1) + (mbV pkSeed pkRoot msgW s &&& 1)
def csumV : Word := 8 - dsumV pkSeed pkRoot msgW s
def wotsInitV : Word := tlInit pkSeed (adrsW 1 (idxLeafV pkSeed pkRoot msgW s) 0 0)
def leafPkV : Word :=
  (List.ofFn fun i : Fin 12 => chainTopW pkSeed (idxLeafV pkSeed pkRoot msgW s) i.val
    (digitW (mbV pkSeed pkRoot msgW s) (csumV pkSeed pkRoot msgW s) i.val) (s.w i)).foldl mix
    (wotsInitV pkSeed pkRoot msgW s)
def rootV : Word := hW pkSeed (adrsW 2 0 1 0) (leafPkV pkSeed pkRoot msgW s) s.xa
def fpConstV : Word := fC + pkSeed + adrsC + idxLeafV pkSeed pkRoot msgW s

/-! ## (b) demoVerifyWords equals the branch-free root comparison. -/

theorem demoVerifyWords_eq :
    demoVerifyWords pkSeed pkRoot msgW s = decide (rootV pkSeed pkRoot msgW s = pkRoot) := by
  simp only [demoVerifyWords, rootV, leafPkV, wotsInitV, csumV, dsumV, mbV, forsPkV,
    root0V, root1V, leaf0V, leaf1V, idxLeafV, f0V, f1V, hmV, fors_swap]
  rfl

/-! ## (a) Block effects. -/

/-- Read slot `k` of the input region at a literal dword offset `o = 8k`. -/
theorem load_slot (rf0 : RegFile) (hx10 : rf0.get .x10 = inputBase)
    (k : ℕ) (o : BitVec 12) (hk : k < 21) (hko : (signExtend12 o).toNat = 8 * k) :
    Region.dwordAt (regionOf pkSeed pkRoot msgW s) (rf0.get .x10 + signExtend12 o)
      = (inputWords pkSeed pkRoot msgW s).getD k 0 := by
  apply load_word
  · rw [show (inputWords pkSeed pkRoot msgW s).length = 21 from by simp [inputWords]]; exact hk
  · rw [hx10, show inputBase + signExtend12 o - inputBase = signExtend12 o from by bv_omega, hko]

/-! ### `load` block, one register per lemma (keeps each goal a single
    `execBlock` term so elaboration stays cheap). -/

set_option maxHeartbeats 1000000 in
theorem load_x10 (rf0 : RegFile) (hx10 : rf0.get .x10 = inputBase) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf0 [] loadInstrs).1.get .x10 = inputBase := by
  simp only [loadInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx10

set_option maxHeartbeats 1000000 in
theorem load_x11 (rf0 : RegFile) (hx10 : rf0.get .x10 = inputBase) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf0 [] loadInstrs).1.get .x11 = pkSeed := by
  have L0 := load_slot pkSeed pkRoot msgW s rf0 hx10 0 0 (by omega) (by decide)
  simp only [inputWords, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ] at L0
  simp only [loadInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [L0]

set_option maxHeartbeats 1000000 in
theorem load_x12 (rf0 : RegFile) (hx10 : rf0.get .x10 = inputBase) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf0 [] loadInstrs).1.get .x12 = pkRoot := by
  have L1 := load_slot pkSeed pkRoot msgW s rf0 hx10 1 8 (by omega) (by decide)
  simp only [inputWords, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ] at L1
  simp only [loadInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [L1]

set_option maxHeartbeats 2000000 in
theorem load_x13 (rf0 : RegFile) (hx10 : rf0.get .x10 = inputBase) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf0 [] loadInstrs).1.get .x13
      = idxLeafV pkSeed pkRoot msgW s := by
  have L0 := load_slot pkSeed pkRoot msgW s rf0 hx10 0 0 (by omega) (by decide)
  have L1 := load_slot pkSeed pkRoot msgW s rf0 hx10 1 8 (by omega) (by decide)
  have L2 := load_slot pkSeed pkRoot msgW s rf0 hx10 2 16 (by omega) (by decide)
  have L3 := load_slot pkSeed pkRoot msgW s rf0 hx10 3 24 (by omega) (by decide)
  simp only [inputWords, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ] at L0 L1 L2 L3
  simp only [loadInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [L0, L1, L2, L3]
  simp only [idxLeafV, hmV, hmsgW, mix,
    show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]

set_option maxHeartbeats 4000000 in
theorem load_x14 (rf0 : RegFile) (hx10 : rf0.get .x10 = inputBase) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf0 [] loadInstrs).1.get .x14
      = forsPkV pkSeed pkRoot msgW s := by
  have L0 := load_slot pkSeed pkRoot msgW s rf0 hx10 0 0 (by omega) (by decide)
  have L1 := load_slot pkSeed pkRoot msgW s rf0 hx10 1 8 (by omega) (by decide)
  have L2 := load_slot pkSeed pkRoot msgW s rf0 hx10 2 16 (by omega) (by decide)
  have L3 := load_slot pkSeed pkRoot msgW s rf0 hx10 3 24 (by omega) (by decide)
  have L4 := load_slot pkSeed pkRoot msgW s rf0 hx10 4 32 (by omega) (by decide)
  have L5 := load_slot pkSeed pkRoot msgW s rf0 hx10 5 40 (by omega) (by decide)
  have L6 := load_slot pkSeed pkRoot msgW s rf0 hx10 6 48 (by omega) (by decide)
  have L7 := load_slot pkSeed pkRoot msgW s rf0 hx10 7 56 (by omega) (by decide)
  simp only [inputWords, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ] at L0 L1 L2 L3 L4 L5 L6 L7
  simp only [loadInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [L0, L1, L2, L3, L4, L5, L6, L7]
  simp only [forsPkV, root0V, root1V, leaf0V, leaf1V, idxLeafV, f0V, f1V, hmV, hmsgW,
    tlInit, fW, hW, adrsW, mix,
    show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide,
    show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide,
    show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide,
    show signExtend12 (5 : BitVec 12) = (5 : Word) from by decide,
    show BitVec.toNat (14 : BitVec 6) = 14 from by decide,
    show BitVec.toNat (15 : BitVec 6) = 15 from by decide,
    show BitVec.ofNat 64 3 = (3 : Word) from by decide,
    show BitVec.ofNat 64 4 = (4 : Word) from by decide]
  bv_omega

/-! ### `wsetup` block, one register per lemma. -/

set_option maxHeartbeats 1000000 in
theorem wsetup_x10 (rf1 : RegFile) (hx10 : rf1.get .x10 = inputBase) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x10 = inputBase := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx10

set_option maxHeartbeats 1000000 in
theorem wsetup_x11 (rf1 : RegFile) (hx11 : rf1.get .x11 = pkSeed) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x11 = pkSeed := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx11

set_option maxHeartbeats 1000000 in
theorem wsetup_x12 (rf1 : RegFile) (hx12 : rf1.get .x12 = pkRoot) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x12 = pkRoot := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx12

set_option maxHeartbeats 1000000 in
theorem wsetup_x13 (rf1 : RegFile) (hx13 : rf1.get .x13 = idxLeafV pkSeed pkRoot msgW s) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x13
      = idxLeafV pkSeed pkRoot msgW s := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx13

set_option maxHeartbeats 2000000 in
theorem wsetup_x5 (rf1 : RegFile) (hx14 : rf1.get .x14 = forsPkV pkSeed pkRoot msgW s) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x5
      = mbV pkSeed pkRoot msgW s := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [hx14]
  simp only [mbV, show signExtend12 (255 : BitVec 12) = (255 : Word) from by decide]

/-- Pure linear identity for the checksum: `8 - (0 + Σ bits) = 8 - Σ bits`.
Stated over abstract summands so the popcount bit-terms are treated as opaque
atoms (no bit-blasting). -/
theorem csum_sum (b7 b6 b5 b4 b3 b2 b1 b0 : Word) :
    (8 : Word) - (0 + b7 + b6 + b5 + b4 + b3 + b2 + b1 + b0)
      = 8 - (b7 + b6 + b5 + b4 + b3 + b2 + b1 + b0) := by
  bv_omega

set_option maxHeartbeats 2000000 in
theorem wsetup_x7 (rf1 : RegFile) (hx14 : rf1.get .x14 = forsPkV pkSeed pkRoot msgW s) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x7
      = csumV pkSeed pkRoot msgW s := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [hx14]
  simp only [csumV, dsumV, mbV, Nat.cast_one,
    show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show signExtend12 (255 : BitVec 12) = (255 : Word) from by decide,
    show BitVec.toNat (7 : BitVec 6) = 7 from by decide,
    show BitVec.toNat (6 : BitVec 6) = 6 from by decide,
    show BitVec.toNat (5 : BitVec 6) = 5 from by decide,
    show BitVec.toNat (4 : BitVec 6) = 4 from by decide,
    show BitVec.toNat (3 : BitVec 6) = 3 from by decide,
    show BitVec.toNat (2 : BitVec 6) = 2 from by decide,
    show BitVec.toNat (1 : BitVec 6) = 1 from by decide]
  -- both sides are now `8 - (Σ identical bit-terms)`; close by the abstract
  -- linear identity so the masks are unified, never bit-blasted
  exact csum_sum _ _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
theorem wsetup_x28 (rf1 : RegFile) (hx11 : rf1.get .x11 = pkSeed)
    (hx13 : rf1.get .x13 = idxLeafV pkSeed pkRoot msgW s) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x28
      = fpConstV pkSeed pkRoot msgW s := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [hx11, hx13]
  simp only [fpConstV]

set_option maxHeartbeats 1000000 in
theorem wsetup_x14 (rf1 : RegFile) (hx11 : rf1.get .x11 = pkSeed)
    (hx13 : rf1.get .x13 = idxLeafV pkSeed pkRoot msgW s) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf1 [] wsetupInstrs).1.get .x14
      = wotsInitV pkSeed pkRoot msgW s := by
  simp only [wsetupInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [hx11, hx13]
  simp only [wotsInitV, tlInit, adrsW, mix,
    show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show BitVec.ofNat 64 0 = (0 : Word) from by decide,
    show BitVec.ofNat 64 1 = (1 : Word) from by decide]
  bv_omega

theorem digitW_cases (mb csum : Word) (i : ℕ) :
    digitW mb csum i = 0 ∨ digitW mb csum i = 1 := by
  unfold digitW; split <;> exact and_one_cases _

theorem chainTop_digitW (pk idx wi mb csum : Word) (i : ℕ) :
    chainTopW pk idx i (digitW mb csum i) wi
      = wi + ((fW pk (adrsW 0 idx (BitVec.ofNat 64 i) 0) 0) &&& (digitW mb csum i - 1)) :=
  chainTop_branchless pk idx wi (digitW mb csum i) i (digitW_cases mb csum i)

theorem base_eq (i : ℕ) :
    fW pkSeed (adrsW 0 (idxLeafV pkSeed pkRoot msgW s) (BitVec.ofNat 64 i) 0) 0
      = fpConstV pkSeed pkRoot msgW s + BitVec.ofNat 64 i := by
  simp only [fW, adrsW, mix, fpConstV]; bv_omega

theorem leafPk_bf :
    leafPkV pkSeed pkRoot msgW s
      = (List.ofFn (fun i : Fin 12 =>
          s.w i + ((fpConstV pkSeed pkRoot msgW s + BitVec.ofNat 64 i.val)
            &&& (digitW (mbV pkSeed pkRoot msgW s) (csumV pkSeed pkRoot msgW s) i.val - 1)))).foldl
          mix (wotsInitV pkSeed pkRoot msgW s) := by
  simp only [leafPkV, chainTop_digitW, base_eq]

theorem w_slot (j : Fin 12) : (inputWords pkSeed pkRoot msgW s).getD (8 + j.val) 0 = s.w j := by
  fin_cases j <;> simp [inputWords, List.ofFn_succ, List.ofFn_zero]

theorem load_w (rf2 : RegFile) (hx10 : rf2.get .x10 = inputBase) (j : Fin 12) (o : BitVec 12)
    (ho : (signExtend12 o).toNat = 8 * (8 + j.val)) :
    Region.dwordAt (regionOf pkSeed pkRoot msgW s) (rf2.get .x10 + signExtend12 o) = s.w j := by
  rw [load_slot pkSeed pkRoot msgW s rf2 hx10 (8 + j.val) o (by omega) ho, w_slot]

theorem add_sext_negone (x : Word) : x + signExtend12 (-1) = x - 1 := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]; bv_omega

theorem ofFn12 {α : Type _} (f : Fin 12 → α) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] := by
  simp only [List.ofFn_succ, List.ofFn_zero]; rfl

set_option maxHeartbeats 4000000 in
theorem wots_x14 (rf2 : RegFile)
    (hx10 : rf2.get .x10 = inputBase)
    (hx5 : rf2.get .x5 = mbV pkSeed pkRoot msgW s)
    (hx7 : rf2.get .x7 = csumV pkSeed pkRoot msgW s)
    (hx28 : rf2.get .x28 = fpConstV pkSeed pkRoot msgW s)
    (hx14 : rf2.get .x14 = wotsInitV pkSeed pkRoot msgW s) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf2 [] wotsInstrs).1.get .x14
      = leafPkV pkSeed pkRoot msgW s := by
  have W0 := load_w pkSeed pkRoot msgW s rf2 hx10 0 64 (by decide)
  have W1 := load_w pkSeed pkRoot msgW s rf2 hx10 1 72 (by decide)
  have W2 := load_w pkSeed pkRoot msgW s rf2 hx10 2 80 (by decide)
  have W3 := load_w pkSeed pkRoot msgW s rf2 hx10 3 88 (by decide)
  have W4 := load_w pkSeed pkRoot msgW s rf2 hx10 4 96 (by decide)
  have W5 := load_w pkSeed pkRoot msgW s rf2 hx10 5 104 (by decide)
  have W6 := load_w pkSeed pkRoot msgW s rf2 hx10 6 112 (by decide)
  have W7 := load_w pkSeed pkRoot msgW s rf2 hx10 7 120 (by decide)
  have W8 := load_w pkSeed pkRoot msgW s rf2 hx10 8 128 (by decide)
  have W9 := load_w pkSeed pkRoot msgW s rf2 hx10 9 136 (by decide)
  have W10 := load_w pkSeed pkRoot msgW s rf2 hx10 10 144 (by decide)
  have W11 := load_w pkSeed pkRoot msgW s rf2 hx10 11 152 (by decide)
  simp only [wotsInstrs, wotsChainInstrs, List.cons_append, List.nil_append, List.append_assoc,
    execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [W0, W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, hx5, hx7, hx28, hx14]
  rw [leafPk_bf, ofFn12]
  simp only [List.foldl_cons, List.foldl_nil, mix, digitW, add_sext_negone,
    Nat.reduceLT, Nat.reduceSub, reduceIte,
    show ((0:Fin 12):ℕ) = 0 from by decide, show ((1:Fin 12):ℕ) = 1 from by decide,
    show ((2:Fin 12):ℕ) = 2 from by decide, show ((3:Fin 12):ℕ) = 3 from by decide,
    show ((4:Fin 12):ℕ) = 4 from by decide, show ((5:Fin 12):ℕ) = 5 from by decide,
    show ((6:Fin 12):ℕ) = 6 from by decide, show ((7:Fin 12):ℕ) = 7 from by decide,
    show ((8:Fin 12):ℕ) = 8 from by decide, show ((9:Fin 12):ℕ) = 9 from by decide,
    show ((10:Fin 12):ℕ) = 10 from by decide, show ((11:Fin 12):ℕ) = 11 from by decide,
    show signExtend12 (0:BitVec 12) = (0:Word) from by decide,
    show signExtend12 (1:BitVec 12) = (1:Word) from by decide,
    show signExtend12 (2:BitVec 12) = (2:Word) from by decide,
    show signExtend12 (3:BitVec 12) = (3:Word) from by decide,
    show signExtend12 (4:BitVec 12) = (4:Word) from by decide,
    show signExtend12 (5:BitVec 12) = (5:Word) from by decide,
    show signExtend12 (6:BitVec 12) = (6:Word) from by decide,
    show signExtend12 (7:BitVec 12) = (7:Word) from by decide,
    show signExtend12 (8:BitVec 12) = (8:Word) from by decide,
    show signExtend12 (9:BitVec 12) = (9:Word) from by decide,
    show signExtend12 (10:BitVec 12) = (10:Word) from by decide,
    show signExtend12 (11:BitVec 12) = (11:Word) from by decide,
    show BitVec.ofNat 64 0 = (0:Word) from by decide,
    show BitVec.ofNat 64 1 = (1:Word) from by decide,
    show BitVec.ofNat 64 2 = (2:Word) from by decide,
    show BitVec.ofNat 64 3 = (3:Word) from by decide,
    show BitVec.ofNat 64 4 = (4:Word) from by decide,
    show BitVec.ofNat 64 5 = (5:Word) from by decide,
    show BitVec.ofNat 64 6 = (6:Word) from by decide,
    show BitVec.ofNat 64 7 = (7:Word) from by decide,
    show BitVec.ofNat 64 8 = (8:Word) from by decide,
    show BitVec.ofNat 64 9 = (9:Word) from by decide,
    show BitVec.ofNat 64 10 = (10:Word) from by decide,
    show BitVec.ofNat 64 11 = (11:Word) from by decide,
    show BitVec.toNat (0:BitVec 6) = 0 from by decide,
    show BitVec.toNat (1:BitVec 6) = 1 from by decide,
    show BitVec.toNat (2:BitVec 6) = 2 from by decide,
    show BitVec.toNat (3:BitVec 6) = 3 from by decide,
    show BitVec.toNat (4:BitVec 6) = 4 from by decide,
    show BitVec.toNat (5:BitVec 6) = 5 from by decide,
    show BitVec.toNat (6:BitVec 6) = 6 from by decide,
    show BitVec.toNat (7:BitVec 6) = 7 from by decide]


set_option maxHeartbeats 2000000 in
theorem wots_x10 (rf2 : RegFile) (hx10 : rf2.get .x10 = inputBase) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf2 [] wotsInstrs).1.get .x10 = inputBase := by
  simp only [wotsInstrs, wotsChainInstrs, List.cons_append, List.nil_append, List.append_assoc,
    execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx10

set_option maxHeartbeats 2000000 in
theorem wots_x11 (rf2 : RegFile) (hx11 : rf2.get .x11 = pkSeed) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf2 [] wotsInstrs).1.get .x11 = pkSeed := by
  simp only [wotsInstrs, wotsChainInstrs, List.cons_append, List.nil_append, List.append_assoc,
    execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx11

set_option maxHeartbeats 2000000 in
theorem wots_x12 (rf2 : RegFile) (hx12 : rf2.get .x12 = pkRoot) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf2 [] wotsInstrs).1.get .x12 = pkRoot := by
  simp only [wotsInstrs, wotsChainInstrs, List.cons_append, List.nil_append, List.append_assoc,
    execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hx12

theorem xa_slot : (inputWords pkSeed pkRoot msgW s).getD 20 0 = s.xa := by
  simp [inputWords, List.ofFn_succ, List.ofFn_zero]

/-- The XMSS root: the `final` block's accumulator (before the compare) equals
`rootV`.  Proved with `leafPkV` generalized so the arithmetic runs on a small
goal. -/
theorem xmss_root :
    hC + pkSeed + (adrsC + signExtend12 3) + leafPkV pkSeed pkRoot msgW s + s.xa
      = rootV pkSeed pkRoot msgW s := by
  simp only [rootV, hW, adrsW, mix,
    show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide,
    show BitVec.ofNat 64 0 = (0 : Word) from by decide,
    show BitVec.ofNat 64 1 = (1 : Word) from by decide,
    show BitVec.ofNat 64 2 = (2 : Word) from by decide]
  generalize leafPkV pkSeed pkRoot msgW s = l
  bv_omega

set_option maxHeartbeats 2000000 in
theorem final_effect (rf3 : RegFile)
    (hx10 : rf3.get .x10 = inputBase) (hx11 : rf3.get .x11 = pkSeed)
    (hx12 : rf3.get .x12 = pkRoot) (hx14 : rf3.get .x14 = leafPkV pkSeed pkRoot msgW s) :
    (execBlock (regionOf pkSeed pkRoot msgW s) 0 rf3 [] finalInstrs).1.get .x10
      = if demoVerifyWords pkSeed pkRoot msgW s then 1 else 0 := by
  have X : Region.dwordAt (regionOf pkSeed pkRoot msgW s) (rf3.get .x10 + signExtend12 160) = s.xa := by
    rw [load_slot pkSeed pkRoot msgW s rf3 hx10 20 160 (by omega) (by decide), xa_slot]
  simp only [finalInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [X, hx11, hx12, hx14]
  simp only [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    xmss_root, eq_select, demoVerifyWords_eq, decide_eq_true_eq]

theorem words_len (pkSeed pkRoot msgW : Word) (s : SigWords) :
    (wordsBytes (inputWords pkSeed pkRoot msgW s)).length = 168 := by
  rw [wordsBytes_length]; simp [inputWords]

theorem execBlock_snd_nil (ro : Region) (b : Word) (rf : RegFile) (is : List Instr) :
    (execBlock ro b rf [] is).2 = [] :=
  List.eq_nil_of_length_eq_zero (by simp [execBlock_ws_length])

/-! ## Per-block memory VCs: all dword loads land aligned inside the region. -/

set_option maxHeartbeats 4000000 in
theorem loadBlock_mem (pkSeed pkRoot msgW : Word) (s : SigWords) (rf : RegFile)
    (hpre : rf.get .x10 = inputBase) :
    blockVCs (regionOf pkSeed pkRoot msgW s) 0 rf [] loadInstrs := by
  simp only [loadInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem, storeSem,
    blockVCs, Region.loadOk, inRw, List.length_nil, RegFile.get_set_self, RegFile.get_set_ne,
    ne_eq, reduceCtorEq, not_false_eq_true]
  rw [hpre, words_len]
  and_intros <;> first | trivial | (rw [if_neg (by decide)]; decide)

set_option maxHeartbeats 4000000 in
theorem wotsBlock_mem (pkSeed pkRoot msgW : Word) (s : SigWords) (rf : RegFile)
    (hpre : rf.get .x10 = inputBase) :
    blockVCs (regionOf pkSeed pkRoot msgW s) 0 rf [] wotsInstrs := by
  simp only [wotsInstrs, wotsChainInstrs, List.cons_append, List.nil_append, List.append_assoc,
    execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem, storeSem,
    blockVCs, Region.loadOk, inRw, List.length_nil, RegFile.get_set_self, RegFile.get_set_ne,
    ne_eq, reduceCtorEq, not_false_eq_true]
  rw [hpre, words_len]
  and_intros <;> first | trivial | (rw [if_neg (by decide)]; decide)

theorem finalBlock_mem (pkSeed pkRoot msgW : Word) (s : SigWords) (rf : RegFile)
    (hpre : rf.get .x10 = inputBase) :
    blockVCs (regionOf pkSeed pkRoot msgW s) 0 rf [] finalInstrs := by
  simp only [finalInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem, storeSem,
    blockVCs, Region.loadOk, inRw, List.length_nil, RegFile.get_set_self, RegFile.get_set_ne,
    ne_eq, reduceCtorEq, not_false_eq_true]
  rw [hpre, words_len]
  and_intros <;> first | trivial | (rw [if_neg (by decide)]; decide)

/-! ## The full functional-correctness spec of the RV64 verifier. -/

set_option maxHeartbeats 4000000 in
theorem slhVerifyFn_spec (pkSeed pkRoot msgW : Word) (s : SigWords) (base : Word) :
    (slhVerifyFn pkSeed pkRoot msgW s).Spec base := by
  vcgen
  case region => exact ⟨slhVerify_region_wf pkSeed pkRoot msgW s, RwRegion.empty_wf⟩
  case slhVerify.load.mem =>
    intro rf ws A hws hpre
    simp only [slhVerifyFn] at hpre
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    exact loadBlock_mem pkSeed pkRoot msgW s rf hpre
  case slhVerify.wots.mem =>
    intro rf ws A hws hreach
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [slhVerifyFn, Stmt.sp] at hreach
    obtain ⟨rfS, wsS, hwsS, hL, hrfS, hwsSeq⟩ := hreach
    obtain ⟨rf0, ws0, hws0, hpre0, hrf0, hws0eq⟩ := hL
    obtain rfl : ws0 = [] := List.eq_nil_of_length_eq_zero hws0
    subst_vars
    simp only [execBlock_snd_nil]
    exact wotsBlock_mem pkSeed pkRoot msgW s _
      (wsetup_x10 pkSeed pkRoot msgW s _ (load_x10 pkSeed pkRoot msgW s rf0 hpre0))
  case slhVerify.final.mem =>
    intro rf ws A hws hreach
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [slhVerifyFn, Stmt.sp] at hreach
    obtain ⟨rfW, wsW, hwsW, hS, hrfW, hwsWeq⟩ := hreach
    obtain ⟨rfS, wsS, hwsS, hL, hrfS, hwsSeq⟩ := hS
    obtain ⟨rf0, ws0, hws0, hpre0, hrf0, hws0eq⟩ := hL
    obtain rfl : ws0 = [] := List.eq_nil_of_length_eq_zero hws0
    subst_vars
    simp only [execBlock_snd_nil]
    exact finalBlock_mem pkSeed pkRoot msgW s _
      (wots_x10 pkSeed pkRoot msgW s _
        (wsetup_x10 pkSeed pkRoot msgW s _ (load_x10 pkSeed pkRoot msgW s rf0 hpre0)))
  case slhVerify.post =>
    intro rf ws A h
    simp only [slhVerifyFn, Stmt.sp] at h
    obtain ⟨rfF, wsF, hwsF, hW, hrfF, hwsFeq⟩ := h
    obtain ⟨rfW, wsW, hwsW, hS, hrfW, hwsWeq⟩ := hW
    obtain ⟨rfS, wsS, hwsS, hL, hrfS, hwsSeq⟩ := hS
    obtain ⟨rf0, ws0, hws0, hpre0, hrf0, hws0eq⟩ := hL
    obtain rfl : ws0 = [] := List.eq_nil_of_length_eq_zero hws0
    subst_vars
    simp only [slhVerifyFn, execBlock_snd_nil]
    refine final_effect pkSeed pkRoot msgW s _ ?_ ?_ ?_ ?_
    · exact wots_x10 pkSeed pkRoot msgW s _
        (wsetup_x10 pkSeed pkRoot msgW s _ (load_x10 pkSeed pkRoot msgW s rf0 hpre0))
    · exact wots_x11 pkSeed pkRoot msgW s _
        (wsetup_x11 pkSeed pkRoot msgW s _ (load_x11 pkSeed pkRoot msgW s rf0 hpre0))
    · exact wots_x12 pkSeed pkRoot msgW s _
        (wsetup_x12 pkSeed pkRoot msgW s _ (load_x12 pkSeed pkRoot msgW s rf0 hpre0))
    · exact wots_x14 pkSeed pkRoot msgW s _
        (wsetup_x10 pkSeed pkRoot msgW s _ (load_x10 pkSeed pkRoot msgW s rf0 hpre0))
        (wsetup_x5 pkSeed pkRoot msgW s _ (load_x14 pkSeed pkRoot msgW s rf0 hpre0))
        (wsetup_x7 pkSeed pkRoot msgW s _ (load_x14 pkSeed pkRoot msgW s rf0 hpre0))
        (wsetup_x28 pkSeed pkRoot msgW s _ (load_x11 pkSeed pkRoot msgW s rf0 hpre0)
          (load_x13 pkSeed pkRoot msgW s rf0 hpre0))
        (wsetup_x14 pkSeed pkRoot msgW s _ (load_x11 pkSeed pkRoot msgW s rf0 hpre0)
          (load_x13 pkSeed pkRoot msgW s rf0 hpre0))

/-! ## Capstone: the RV64 program matches FIPS 205 verification. -/

/-- The verifier's postcondition, at the packed message word, is exactly the
FIPS 205 verification result: `a0 = 1` iff `slhVerifyInternal` accepts.
Combined with `slhVerifyFn_spec` this gives end-to-end correctness of the
emitted RV64 machine code against the ported SLH-DSA specification. -/
theorem slhVerifyFn_post_fips (pkSeed pkRoot : Word) (msg : List Byte) (s : SigWords)
    (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion) :
    (slhVerifyFn pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) s).post rf ws A
      ↔ rf.get .x10 = if slhVerifyInternal demoPrims msg s.toSig ⟨pkSeed, pkRoot⟩ then 1 else 0 := by
  simp only [slhVerifyFn, demoVerifyWords_correct]

end SlhVerify
end EvmAsm.Rv64
