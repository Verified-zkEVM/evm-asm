/-
  EvmAsm.SLHDSA.DemoCorrect

  Correctness of the word-level reference verifier: `Demo.demoVerifyWords`
  computes exactly the ported FIPS 205 verification algorithm
  `SLHDSA.slhVerifyInternal` at the demonstration instance `Demo.demoPrims`
  (`demoVerifyWords_correct`).

  The proof is a chain of per-component equations: the `H_msg` digest split
  (`splitDigest_demo`), the FORS leaf indices (`forsIdx_demo_*`), one-level
  Merkle climbs (`Merkle.climb_one`), the `w = 2` chain completion
  (`chain_demo`), the FORS public-key recovery (`forsPkFromSig_demo`), the
  WOTS+ digit vector (`chainSteps_demo`), and the WOTS+ public-key recovery
  (`wotsPkFromSig_demo`), each bridging the specification's ℕ-level digit
  arithmetic to the RV64 word operations.
-/

module
public import EvmAsm.SLHDSA.DemoInstance
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SLHDSA
namespace Demo

/-! ## Word/ℕ bridges -/

theorem bv_and_one (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega

theorem bv_shr_and_one (x : BitVec 64) (k : ℕ) :
    (x >>> k) &&& 1 = BitVec.ofNat 64 (x.toNat >>> k % 2) := by
  rw [bv_and_one, BitVec.toNat_ushiftRight]

theorem bv_ofNat_eq_zero_iff {n : ℕ} (h : n < 2) :
    (BitVec.ofNat 64 n = 0) ↔ n = 0 := by
  rw [BitVec.toNat_eq]
  rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
  omega

theorem bv_ofNat_eq_one_iff {n : ℕ} (h : n < 2) :
    (BitVec.ofNat 64 n = 1) ↔ n = 1 := by
  rw [BitVec.toNat_eq]
  rw [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem bv_and_ff (x : BitVec 64) : x &&& 0xff = BitVec.ofNat 64 (x.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (0xff : BitVec 64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## One-level Merkle climbs and `w = 2` chains -/

/-- Climbing a single-node authentication path is one node hash, ordered by
the leaf-index parity. -/
theorem Merkle.climb_one {Y : Type} (nh : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node a : Y) :
    SLHDSA.Merkle.climb nh 0 idx node [a]
      = if idx % 2 = 0 then nh 1 (idx / 2) node a else nh 1 (idx / 2) a node := rfl

/-- For `w = 2`, completing a chain from digit `d` is a single `F` step at
hash address 0 when `d = 0` and the identity when `d = 1`. -/
theorem chain_demo (pk : BitVec 64) (adrs : Adrs) (x : BitVec 64) (d : ℕ) (hd : d < 2) :
    chain demoPrims pk adrs x d (demoParams.w - 1 - d)
      = if d = 1 then x else demoPrims.F pk (adrs.setHashAddress 0) x := by
  have hd2 : d = 0 ∨ d = 1 := by omega
  rcases hd2 with rfl | rfl
  · rfl
  · rfl

/-! ## The digest split -/

/-- The `H_msg` digest split at the demonstration instance: the FORS message
is the digest's first byte (bits 15–8 of the `H_msg` word), the hypertree
leaf index its lowest bit. -/
private theorem splitDigest_two (d : Bytes demoParams.m) (b0 b1 : Byte)
    (h : d.toList = [b0, b1]) :
    splitDigest demoParams d = ([b0], b1.toNat % 2) := by
  unfold splitDigest
  rw [h]
  refine Prod.ext rfl ?_
  show toInt [b1] % 2 ^ 1 = b1.toNat % 2
  unfold toInt
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add, pow_one]

theorem splitDigest_demo (r pk root : BitVec 64) (msg : List Byte) :
    splitDigest demoParams (demoPrims.Hmsg r pk root msg)
      = ([UInt8.ofNat ((hmsgW r pk root (BitVec.ofNat 64 (toInt msg))).toNat >>> 8 % 256)],
         (hmsgW r pk root (BitVec.ofNat 64 (toInt msg))).toNat % 2) := by
  rw [splitDigest_two (demoPrims.Hmsg r pk root msg)
    (UInt8.ofNat ((hmsgW r pk root (BitVec.ofNat 64 (toInt msg))).toNat >>> 8 % 256))
    (UInt8.ofNat ((hmsgW r pk root (BitVec.ofNat 64 (toInt msg))).toNat % 256)) rfl]
  refine Prod.ext rfl ?_
  show (UInt8.ofNat ((hmsgW r pk root (BitVec.ofNat 64 (toInt msg))).toNat % 256)).toNat % 2
      = (hmsgW r pk root (BitVec.ofNat 64 (toInt msg))).toNat % 2
  rw [UInt8.toNat_ofNat']
  omega

/-! ## FORS leaf indices -/

theorem base2b_byte_two (b : Byte) :
    base2b [b] 1 2 = [b.toNat >>> 7 % 2, b.toNat >>> 6 % 2] := by
  simp [base2b, base2bGo, base2bFill]

theorem forsIdx_demo_zero (b : Byte) :
    forsIdx demoParams [b] 0 = b.toNat >>> 7 % 2 := by
  unfold forsIdx
  rw [show demoParams.a = 1 from rfl, show demoParams.k = 2 from rfl, base2b_byte_two]
  rfl

theorem forsIdx_demo_one (b : Byte) :
    forsIdx demoParams [b] 1 = b.toNat >>> 6 % 2 := by
  unfold forsIdx
  rw [show demoParams.a = 1 from rfl, show demoParams.k = 2 from rfl, base2b_byte_two]
  rfl

/-! ## FORS public-key recovery -/

private theorem finRange_k :
    List.finRange demoParams.k = [⟨0, by decide⟩, ⟨1, by decide⟩] := by decide

private theorem map_pair {α β : Type} (f : α → β) (x y : α) :
    List.map f [x, y] = [f x, f y] := rfl

/-- FORS public-key recovery at the demonstration instance, as a word
computation over the two revealed leaves and auth nodes.  The digit
conditions and address words are stated over the ℕ-level digits
`b.toNat >>> 7 % 2` / `b.toNat >>> 6 % 2`. -/
theorem forsPkFromSig_demo (pk s0 a0 s1 a1 : BitVec 64) (b : Byte) (iN : ℕ) :
    forsPkFromSig demoPrims ⟨#[(s0, [a0]), (s1, [a1])], rfl⟩ [b] pk (forsAdrsOf iN)
      = (let iW := BitVec.ofNat 64 iN
         let f0 := b.toNat >>> 7 % 2
         let f1 := b.toNat >>> 6 % 2
         let leaf0 := fW pk (adrsW 3 iW 0 (BitVec.ofNat 64 f0)) s0
         let root0 := if f0 = 0 then hW pk (adrsW 3 iW 1 0) leaf0 a0
                      else hW pk (adrsW 3 iW 1 0) a0 leaf0
         let leaf1 := fW pk (adrsW 3 iW 0 (BitVec.ofNat 64 (2 + f1))) s1
         let root1 := if f1 = 0 then hW pk (adrsW 3 iW 1 1) leaf1 a1
                      else hW pk (adrsW 3 iW 1 1) a1 leaf1
         mix (mix (tlInit pk (adrsW 4 iW 0 0)) root0) root1) := by
  have hf0 : forsIdx demoParams [b] 0 = b.toNat >>> 7 % 2 := forsIdx_demo_zero b
  have hf1 : forsIdx demoParams [b] 1 = b.toNat >>> 6 % 2 := forsIdx_demo_one b
  have hf0lt : b.toNat >>> 7 % 2 < 2 := Nat.mod_lt _ (by omega)
  have hf1lt : b.toNat >>> 6 % 2 < 2 := Nat.mod_lt _ (by omega)
  -- abstract the two digit values and split on them: each of the four cases
  -- is then a definitional computation
  generalize hg0 : b.toNat >>> 7 % 2 = f0N at hf0 hf0lt ⊢
  generalize hg1 : b.toNat >>> 6 % 2 = f1N at hf1 hf1lt ⊢
  have h0 : f0N = 0 ∨ f0N = 1 := by omega
  have h1 : f1N = 0 ∨ f1N = 1 := by omega
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
    · unfold forsPkFromSig
      rw [finRange_k]
      simp only [map_pair]
      rw [hf0, hf1]
      norm_num [Merkle.climb, show demoParams.a = 1 from rfl]
      rfl

/-! ## WOTS+ digits -/

theorem base2b_byte_eight (b : Byte) :
    base2b [b] 1 8 = [b.toNat >>> 7 % 2, b.toNat >>> 6 % 2, b.toNat >>> 5 % 2,
      b.toNat >>> 4 % 2, b.toNat >>> 3 % 2, b.toNat >>> 2 % 2, b.toNat >>> 1 % 2,
      b.toNat >>> 0 % 2] := by
  simp [base2b, base2bGo, base2bFill]

private theorem digitsOfBaseW_two_four (n : ℕ) :
    WotsChecksum.digitsOfBaseW n 2 4 = [n / 8 % 2, n / 4 % 2, n / 2 % 2, n % 2] := by
  show ((n / 2 ^ 3) % 2) :: ((n / 2 ^ 2) % 2) :: ((n / 2 ^ 1) % 2) :: ((n / 2 ^ 0) % 2) :: []
    = [n / 8 % 2, n / 4 % 2, n / 2 % 2, n % 2]
  norm_num

set_option maxHeartbeats 1000000 in
private theorem bv_sub_sum_digits (d7 d6 d5 d4 d3 d2 d1 d0 : ℕ)
    (h7 : d7 < 2) (h6 : d6 < 2) (h5 : d5 < 2) (h4 : d4 < 2)
    (h3 : d3 < 2) (h2 : d2 < 2) (h1 : d1 < 2) (h0 : d0 < 2) :
    (8 : BitVec 64) - (BitVec.ofNat 64 d7 + BitVec.ofNat 64 d6 + BitVec.ofNat 64 d5
        + BitVec.ofNat 64 d4 + BitVec.ofNat 64 d3 + BitVec.ofNat 64 d2
        + BitVec.ofNat 64 d1 + BitVec.ofNat 64 d0)
      = BitVec.ofNat 64 (8 - (d7 + d6 + d5 + d4 + d3 + d2 + d1 + d0)) := by
  bv_omega

private theorem checksum_sum_eq (d7 d6 d5 d4 d3 d2 d1 d0 : ℕ)
    (h7 : d7 < 2) (h6 : d6 < 2) (h5 : d5 < 2) (h4 : d4 < 2)
    (h3 : d3 < 2) (h2 : d2 < 2) (h1 : d1 < 2) (h0 : d0 < 2) :
    WotsChecksum.wotsChecksumValue 2 [d7, d6, d5, d4, d3, d2, d1, d0]
      = 8 - (d7 + d6 + d5 + d4 + d3 + d2 + d1 + d0) := by
  unfold WotsChecksum.wotsChecksumValue
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The checksum value of the demonstration digit vector, as a plain ℕ
expression over the committed byte `B`. -/
def csumN (B : ℕ) : ℕ :=
  8 - (B >>> 7 % 2 + B >>> 6 % 2 + B >>> 5 % 2 + B >>> 4 % 2
    + B >>> 3 % 2 + B >>> 2 % 2 + B >>> 1 % 2 + B >>> 0 % 2)

/-- The twelve WOTS+ chain digits at the demonstration instance: the eight
bits of the node's low byte (most significant first) followed by the four
bits of the checksum `8 - Σ dᵢ`. -/
theorem chainLengths_demo (y : BitVec 64) :
    chainLengths demoPrims y
      = (let B := y.toNat % 256
         let s := B >>> 7 % 2 + B >>> 6 % 2 + B >>> 5 % 2 + B >>> 4 % 2
           + B >>> 3 % 2 + B >>> 2 % 2 + B >>> 1 % 2 + B >>> 0 % 2
         [B >>> 7 % 2, B >>> 6 % 2, B >>> 5 % 2, B >>> 4 % 2,
          B >>> 3 % 2, B >>> 2 % 2, B >>> 1 % 2, B >>> 0 % 2,
          (8 - s) / 8 % 2, (8 - s) / 4 % 2, (8 - s) / 2 % 2, (8 - s) % 2]) := by
  have hb : (demoPrims.yToBytes y).toList = [UInt8.ofNat (y.toNat % 256)] := rfl
  have hbn : (UInt8.ofNat (y.toNat % 256)).toNat = y.toNat % 256 := by
    rw [UInt8.toNat_ofNat', show (2 : ℕ) ^ 8 = 256 from rfl]; omega
  unfold chainLengths wotsMsgDigits WotsChecksum.wotsFullDigits
  rw [hb]
  rw [show demoParams.lgw = 1 from rfl, show demoParams.len1 = 8 from rfl,
    show demoParams.len2 = 4 from demoParams_len2, show demoParams.w = 2 from rfl]
  rw [base2b_byte_eight, hbn]
  have hlt : ∀ k : ℕ, (y.toNat % 256) >>> k % 2 < 2 := fun k => Nat.mod_lt _ (by omega)
  rw [checksum_sum_eq ((y.toNat % 256) >>> 7 % 2) ((y.toNat % 256) >>> 6 % 2)
      ((y.toNat % 256) >>> 5 % 2) ((y.toNat % 256) >>> 4 % 2) ((y.toNat % 256) >>> 3 % 2)
      ((y.toNat % 256) >>> 2 % 2) ((y.toNat % 256) >>> 1 % 2) ((y.toNat % 256) >>> 0 % 2)
      (hlt 7) (hlt 6) (hlt 5) (hlt 4) (hlt 3) (hlt 2) (hlt 1) (hlt 0),
    digitsOfBaseW_two_four]
  rfl

/-! ## WOTS+ public-key recovery -/

private theorem ofFn_len_cast {α : Type} {m n : ℕ} (h : m = n) (f : Fin m → α) :
    List.ofFn f = List.ofFn fun i : Fin n => f (Fin.cast h.symm i) := by
  subst h; rfl

/-- WOTS+ public-key recovery at the demonstration instance, as a fold of
the twelve completed chain tops (each an `ite` on its ℕ-level digit
`chainSteps`). -/
theorem wotsPkFromSig_demo (pk y : BitVec 64) (w : Fin 12 → BitVec 64) (iN : ℕ) :
    wotsPkFromSig demoPrims
        (Vector.ofFn fun j : Fin demoParams.len => w (Fin.cast demoParams_len j)) y pk
        (wotsLeafAdrs (htAdrs Adrs.zero 0) iN)
      = (List.ofFn fun i : Fin 12 =>
          if chainSteps demoPrims y i.val = 1 then w i
          else fW pk (adrsW 0 (BitVec.ofNat 64 iN) (BitVec.ofNat 64 i.val) 0) (w i)).foldl
          mix (tlInit pk (adrsW 1 (BitVec.ofNat 64 iN) 0 0)) := by
  show (wotsPkFromSigTops demoPrims _ y pk
      (wotsLeafAdrs (htAdrs Adrs.zero 0) iN)).toList.foldl mix
      (tlInit pk (adrsW 1 (BitVec.ofNat 64 iN) 0 0)) = _
  unfold wotsPkFromSigTops
  rw [Vector.toList_ofFn]
  rw [ofFn_len_cast demoParams_len]
  refine congrArg (fun l => List.foldl mix (tlInit pk (adrsW 1 (BitVec.ofNat 64 iN) 0 0)) l)
    (congrArg List.ofFn (funext fun i => ?_))
  have hel : (Vector.ofFn fun j : Fin demoParams.len => w (Fin.cast demoParams_len j))[i.val]'
      (demoParams_len.symm ▸ i.isLt) = w i := by
    rw [Vector.getElem_ofFn]
    rfl
  show chain demoPrims pk (wotsChainAdrs (wotsLeafAdrs (htAdrs Adrs.zero 0) iN) i.val)
      ((Vector.ofFn fun j : Fin demoParams.len => w (Fin.cast demoParams_len j))[i.val]'
        (demoParams_len.symm ▸ i.isLt))
      (chainSteps demoPrims y i.val) (demoParams.w - 1 - chainSteps demoPrims y i.val)
    = _
  rw [hel, chain_demo pk _ _ _ (chainSteps_lt demoPrims y i.val)]
  rfl

/-! ## The WOTS+ digit bridge: `chainSteps` to `digitW` -/

/-- The twelve completed chain tops, bridged from the specification digits
(`chainSteps`, over ℕ) to the word-level computation (`digitW` over the
committed byte `mb` and checksum `csum` as the RV64 code holds them). -/
theorem chainTops_demo (pk yv iW mb csum : BitVec 64) (iN : ℕ) (w : Fin 12 → BitVec 64)
    (hiW : iW = BitVec.ofNat 64 iN)
    (hmb : mb = yv &&& (0xff : BitVec 64))
    (hcsum : csum = (8 : BitVec 64) - (((mb >>> 7) &&& (1 : BitVec 64))
      + ((mb >>> 6) &&& (1 : BitVec 64)) + ((mb >>> 5) &&& (1 : BitVec 64))
      + ((mb >>> 4) &&& (1 : BitVec 64)) + ((mb >>> 3) &&& (1 : BitVec 64))
      + ((mb >>> 2) &&& (1 : BitVec 64)) + ((mb >>> 1) &&& (1 : BitVec 64))
      + (mb &&& (1 : BitVec 64)))) :
    (List.ofFn fun i : Fin 12 =>
        if chainSteps demoPrims yv i.val = 1 then w i
        else fW pk (adrsW 0 (BitVec.ofNat 64 iN) (BitVec.ofNat 64 i.val) 0) (w i))
      = List.ofFn fun i : Fin 12 =>
          chainTopW pk iW i.val (digitW mb csum i.val) (w i) := by
  -- the digit list, let-free
  have hcl : chainLengths demoPrims yv
      = [(yv.toNat % 256) >>> 7 % 2, (yv.toNat % 256) >>> 6 % 2, (yv.toNat % 256) >>> 5 % 2,
         (yv.toNat % 256) >>> 4 % 2, (yv.toNat % 256) >>> 3 % 2, (yv.toNat % 256) >>> 2 % 2,
         (yv.toNat % 256) >>> 1 % 2, (yv.toNat % 256) >>> 0 % 2,
         csumN (yv.toNat % 256) / 8 % 2, csumN (yv.toNat % 256) / 4 % 2,
         csumN (yv.toNat % 256) / 2 % 2, csumN (yv.toNat % 256) % 2] := by
    rw [chainLengths_demo]
    rfl
  -- word-level values of the committed byte and its bits
  have hmbT : mb.toNat = yv.toNat % 256 := by
    rw [hmb, bv_and_ff, BitVec.toNat_ofNat]
    omega
  have hbit : ∀ k : ℕ, (mb >>> k) &&& 1 = BitVec.ofNat 64 ((yv.toNat % 256) >>> k % 2) := by
    intro k
    rw [bv_shr_and_one, hmbT]
  have hbit0 : mb &&& (1 : BitVec 64) = BitVec.ofNat 64 ((yv.toNat % 256) >>> 0 % 2) := by
    rw [bv_and_one, hmbT, Nat.shiftRight_zero]
  -- the checksum word is the ℕ checksum
  have hd : ∀ k : ℕ, (yv.toNat % 256) >>> k % 2 < 2 := fun k => Nat.mod_lt _ (by omega)
  have hcsumW : csum = BitVec.ofNat 64 (csumN (yv.toNat % 256)) := by
    rw [hcsum, hbit 7, hbit 6, hbit 5, hbit 4, hbit 3, hbit 2, hbit 1, hbit0,
      bv_sub_sum_digits ((yv.toNat % 256) >>> 7 % 2) ((yv.toNat % 256) >>> 6 % 2)
        ((yv.toNat % 256) >>> 5 % 2) ((yv.toNat % 256) >>> 4 % 2)
        ((yv.toNat % 256) >>> 3 % 2) ((yv.toNat % 256) >>> 2 % 2)
        ((yv.toNat % 256) >>> 1 % 2) ((yv.toNat % 256) >>> 0 % 2)
        (hd 7) (hd 6) (hd 5) (hd 4) (hd 3) (hd 2) (hd 1) (hd 0)]
    rfl
  have hcsT : csum.toNat = csumN (yv.toNat % 256) := by
    rw [hcsumW, BitVec.toNat_ofNat]
    have : csumN (yv.toNat % 256) ≤ 8 := by unfold csumN; omega
    omega
  have hcbit : ∀ k : ℕ, (csum >>> k) &&& 1
      = BitVec.ofNat 64 (csumN (yv.toNat % 256) >>> k % 2) := by
    intro k
    rw [bv_shr_and_one, hcsT]
  have hcbit0 : csum &&& (1 : BitVec 64)
      = BitVec.ofNat 64 (csumN (yv.toNat % 256) >>> 0 % 2) := by
    rw [bv_and_one, hcsT, Nat.shiftRight_zero]
  -- shift-to-division for the checksum digits
  have hsd : ∀ n : ℕ, n >>> 3 = n / 8 := fun n => by
    rw [Nat.shiftRight_eq_div_pow]
  have hsd2 : ∀ n : ℕ, n >>> 2 = n / 4 := fun n => by
    rw [Nat.shiftRight_eq_div_pow]
  have hsd1 : ∀ n : ℕ, n >>> 1 = n / 2 := fun n => by
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  refine congrArg List.ofFn (funext fun i => ?_)
  fin_cases i <;>
    simp only [chainSteps, hcl, List.getD_cons_zero, List.getD_cons_succ, chainTopW, digitW,
      hiW, hbit, hcbit, hsd, hsd2, hsd1,
      Nat.sub_zero, Nat.sub_self, if_true, if_false, Nat.shiftRight_zero,
      show ((0:ℕ) < 8) = True from by simp, show ((1:ℕ) < 8) = True from by simp,
      show ((2:ℕ) < 8) = True from by simp, show ((3:ℕ) < 8) = True from by simp,
      show ((4:ℕ) < 8) = True from by simp, show ((5:ℕ) < 8) = True from by simp,
      show ((6:ℕ) < 8) = True from by simp, show ((7:ℕ) < 8) = True from by simp,
      show ((8:ℕ) < 8) = False from by simp, show ((9:ℕ) < 8) = False from by simp,
      show ((10:ℕ) < 8) = False from by simp, show ((11:ℕ) < 8) = False from by simp] <;>
    norm_num <;>
    exact if_congr (bv_ofNat_eq_one_iff (by omega)).symm rfl rfl

/-! ## The main correctness theorem -/

/-- The single-level XMSS auth-path climb at the demonstration instance, for
a leaf index below 2: one `H` call at the height-1 root address, ordered by
the index. -/
private theorem xmss_climb_one (pk node aa : BitVec 64) (idx : ℕ) (hidx : idx < 2) :
    Merkle.climb (fun (z t : ℕ) (l rr : BitVec 64) =>
        xmssNodeHash demoPrims pk (htAdrs Adrs.zero 0) z t l rr) 0 idx node [aa]
      = if idx = 0 then hW pk (adrsW 2 0 1 0) node aa
        else hW pk (adrsW 2 0 1 0) aa node := by
  have h : idx = 0 ∨ idx = 1 := by omega
  rcases h with rfl | rfl <;> rfl

/-- **The word-level reference verifier is the FIPS 205 verifier**:
`demoVerifyWords` computes `slhVerifyInternal` at the demonstration
instance, for every message and every fixed-format signature. -/
theorem demoVerifyWords_correct (msg : List Byte) (pkSeed pkRoot : BitVec 64) (s : SigWords) :
    demoVerifyWords pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) s
      = slhVerifyInternal demoPrims msg s.toSig ⟨pkSeed, pkRoot⟩ := by
  obtain ⟨r, s0, a0, s1, a1, w, xa⟩ := s
  -- unfold the specification verifier in one well-typed step
  rw [show slhVerifyInternal demoPrims msg
        (SigWords.toSig ⟨r, s0, a0, s1, a1, w, xa⟩) ⟨pkSeed, pkRoot⟩
      = decide ((Merkle.climb (fun (z t : ℕ) (l rr : BitVec 64) =>
            xmssNodeHash demoPrims pkSeed (htAdrs Adrs.zero 0) z t l rr) 0
          (splitDigest demoParams (demoPrims.Hmsg r pkSeed pkRoot msg)).2
          (wotsPkFromSig demoPrims
            (Vector.ofFn fun j : Fin demoParams.len => w (Fin.cast demoParams_len j))
            (forsPkFromSig demoPrims ⟨#[(s0, [a0]), (s1, [a1])], rfl⟩
              (splitDigest demoParams (demoPrims.Hmsg r pkSeed pkRoot msg)).1 pkSeed
              (forsAdrsOf (splitDigest demoParams (demoPrims.Hmsg r pkSeed pkRoot msg)).2))
            pkSeed (wotsLeafAdrs (htAdrs Adrs.zero 0)
              (splitDigest demoParams (demoPrims.Hmsg r pkSeed pkRoot msg)).2))
          [xa] : BitVec 64) = pkRoot) from rfl]
  simp only [splitDigest_demo r pkSeed pkRoot msg]
  -- ℕ-level digest-byte facts
  have hbT : (UInt8.ofNat ((hmsgW r pkSeed pkRoot
        (BitVec.ofNat 64 (toInt msg))).toNat >>> 8 % 256)).toNat
      = (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 8 % 256 := by
    rw [UInt8.toNat_ofNat', show (2 : ℕ) ^ 8 = 256 from rfl]
    omega
  have h15 : ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 8 % 256) >>> 7 % 2
      = (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 15 % 2 := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  have h14 : ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 8 % 256) >>> 6 % 2
      = (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 14 % 2 := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  -- FORS public-key recovery, as a word computation
  rw [forsPkFromSig_demo pkSeed s0 a0 s1 a1
    (UInt8.ofNat ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 8 % 256))
    ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat % 2)]
  simp only [hbT, h15, h14]
  -- WOTS+ public-key recovery, as a word computation
  rw [wotsPkFromSig_demo (pk := pkSeed) (w := w)
    (iN := (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat % 2)]
  -- the twelve chain tops, as the word-level digit computation
  rw [chainTops_demo (pk := pkSeed) (w := w)
    (iN := (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat % 2)
    (hiW := rfl) (hmb := rfl) (hcsum := rfl)]
  -- the XMSS auth-path climb (one level)
  rw [xmss_climb_one pkSeed _ xa
    ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat % 2) (by omega)]
  -- bridge every remaining ℕ-level digit back to the word the code holds
  have hw1 : BitVec.ofNat 64 ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat % 2)
      = hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) &&& 1 :=
    (bv_and_one (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)))).symm
  have hw15 : BitVec.ofNat 64
        ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 15 % 2)
      = (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) >>> 15) &&& 1 :=
    (bv_shr_and_one (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))) 15).symm
  have hw14 : BitVec.ofNat 64
        ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 14 % 2)
      = (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) >>> 14) &&& 1 :=
    (bv_shr_and_one (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))) 14).symm
  have hw2f : BitVec.ofNat 64
        (2 + (hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 14 % 2)
      = 2 + ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) >>> 14) &&& 1) := by
    rw [BitVec.ofNat_add, hw14]
    rfl
  have hc1 : ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat % 2 = 0)
      = ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) &&& 1) = 0) := by
    rw [← hw1]
    exact (propext (bv_ofNat_eq_zero_iff (by omega))).symm
  have hc15 : ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 15 % 2 = 0)
      = (((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) >>> 15) &&& 1) = 0) := by
    rw [← hw15]
    exact (propext (bv_ofNat_eq_zero_iff (by omega))).symm
  have hc14 : ((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg))).toNat >>> 14 % 2 = 0)
      = (((hmsgW r pkSeed pkRoot (BitVec.ofNat 64 (toInt msg)) >>> 14) &&& 1) = 0) := by
    rw [← hw14]
    exact (propext (bv_ofNat_eq_zero_iff (by omega))).symm
  simp only [hc15, hc14, hc1, hw2f, hw1, hw15]
  -- unfold the word-level verifier and close
  simp only [demoVerifyWords]
  rfl

end Demo
end SLHDSA
