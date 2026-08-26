/-
  EvmAsm.SLHDSA.VerifySAsm

  A formally verified RV64 implementation of the SLH-DSA (FIPS 205)
  verifier at the demonstration instance `SLHDSA.Demo.demoPrims`
  (EvmAsm/SLHDSA/DemoInstance.lean), written in the SAsm structured-
  assembly DSL.

  Input format (all 64-bit words, little-endian dwords, at the input
  arena base 0x40000000):

    off   0  PK.seed          off  32  FORS tree-0 leaf secret
    off   8  PK.root          off  40  FORS tree-0 auth node
    off  16  randomizer R     off  48  FORS tree-1 leaf secret
    off  24  packed message   off  56  FORS tree-1 auth node
    off  64..152  the twelve WOTS+ chain words
    off 160  XMSS auth node

  Output: a0 = 1 if the signature verifies, 0 otherwise.

  What is verified here:

  - `slhVerifyFn` is the complete SAsm verifier; `slhVerify_program` is
    its emitted machine code. `slhVerify_position_independent` proves the
    code is position-independent and `slhVerify_region_wf` proves the
    input region is well-formed (all loads land in the machine's input
    arena).
  - The word-level reference verifier `Demo.demoVerifyWords` (which the
    SAsm body computes register-for-register) is proved *equal to the
    ported FIPS 205 algorithm* `SLHDSA.slhVerifyInternal` by
    `Demo.demoVerifyWords_correct` (EvmAsm/SLHDSA/DemoCorrect.lean) — the
    cryptographically meaningful correctness result.
  - The bridge lemmas connecting the SAsm engine to `demoVerifyWords`
    (`execInstrRF_mixInstr`, `load_word`, the region model, `fors_swap`,
    `chainTop_branchless`, the branchless-select identities, and the
    load-block engine-collapse recipe) are all proved here; assembling
    them into the full `Fn.Spec` of `slhVerifyFn` is the remaining step.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.SLHDSA.DemoCorrect

namespace EvmAsm.Rv64
namespace SlhVerify

open SAsm SLHDSA SLHDSA.Demo

/-! ## The input region: a list of dwords -/

/-- The input arena base. -/
def inputBase : Word := 0x40000000

/-- Little-endian dword serialization of a word list. -/
def wordsBytes (vs : List Word) : List (BitVec 8) := vs.flatMap dwordBytes

@[simp] theorem wordsBytes_nil : wordsBytes [] = [] := rfl

@[simp] theorem wordsBytes_cons (v : Word) (vs : List Word) :
    wordsBytes (v :: vs) = dwordBytes v ++ wordsBytes vs := by
  simp [wordsBytes]

theorem wordsBytes_length (vs : List Word) : (wordsBytes vs).length = 8 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [wordsBytes_cons, List.length_append, length_dwordBytes, ih, List.length_cons]
    omega

/-- The dword at slot `k` of a serialized word list. -/
theorem packBytes_wordsBytes_slot (vs : List Word) (k : ℕ) (hk : k < vs.length) :
    packBytes (((wordsBytes vs).drop (8 * k)).take 8) = vs.getD k 0 := by
  induction vs generalizing k with
  | nil => simp at hk
  | cons v vs ih =>
    cases k with
    | zero =>
      rw [wordsBytes_cons, Nat.mul_zero]
      exact packDword_at0 v (wordsBytes vs)
    | succ k =>
      rw [wordsBytes_cons, show 8 * (k + 1) = 8 + 8 * k from by omega,
        drop8_dword_append, List.getD_cons_succ]
      exact ih k (by simpa using hk)

/-- Read the dword at slot `k` out of the serialized input region. -/
theorem region_dwordAt (vs : List Word) (k : ℕ) (hk : k < vs.length) (addr : Word)
    (haddr : (addr - inputBase).toNat = 8 * k) :
    Region.dwordAt ⟨inputBase, wordsBytes vs⟩ addr = vs.getD k 0 := by
  unfold Region.dwordAt
  rw [show (⟨inputBase, wordsBytes vs⟩ : Region).base = inputBase from rfl,
    show (⟨inputBase, wordsBytes vs⟩ : Region).bytes = wordsBytes vs from rfl, haddr]
  exact packBytes_wordsBytes_slot vs k hk

/-- The input buffer forms a well-formed SAsm region (dword-aligned base in
the machine's input zone); the statement and proof mirror
`EvmAsm.Rv64.inputRegion_wf` (ChainIdSAsm.lean). -/
theorem slhInputRegion_wf (bs : List (BitVec 8)) (hlen : bs.length ≤ 0x2000) :
    (Region.mk inputBase bs).wf := by
  have hb : (0x40000000 : Word).toNat = 0x40000000 := by decide
  refine ⟨?_, ?_, ?_⟩
  · show (0x40000000 : Word).toNat % 8 = 0
    omega
  · show (0x40000000 : Word).toNat + bs.length < 2 ^ 64
    omega
  · intro k hk
    have hk' : k < bs.length := hk
    show isValidMemAddr ((0x40000000 : Word) + BitVec.ofNat 64 k) = true
    simp only [isValidMemAddr, INPUT_MEM_START, INPUT_MEM_END, MEM_START,
      MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat, hb]
    omega

/-- Load word `k` (at a literal dword offset `o = 8k`) out of the serialized
input region: `region.dwordAt (rf.get x10 + signExtend12 o) = vs[k]`. -/
theorem load_word (vs : List Word) (rf : RegFile) (k : ℕ) (o : BitVec 12)
    (hk : k < vs.length)
    (haddr : ((rf.get .x10 + signExtend12 o) - inputBase).toNat = 8 * k) :
    Region.dwordAt ⟨inputBase, wordsBytes vs⟩ (rf.get .x10 + signExtend12 o) = vs.getD k 0 :=
  region_dwordAt vs k hk _ haddr

/-! ## Branchless-select word identities -/

/-- Every masked-to-one-bit word is 0 or 1. -/
theorem and_one_cases (x : Word) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  rw [bv_and_one]
  have h : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h]
  · left; rfl
  · right; rfl

/-- The branchless two-way pick: `a` when the bit is 0, `b` when it is 1. -/
theorem pick_select (d a b : Word) (hd : d = 0 ∨ d = 1) :
    a ^^^ ((a ^^^ b) &&& (0 - d)) = if d = 1 then b else a := by
  rcases hd with rfl | rfl
  · rw [if_neg (by decide)]
    simp
  · rw [if_pos rfl]
    rw [show (0 : Word) - 1 = BitVec.allOnes 64 from by decide]
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The left output of the branchless swap. -/
theorem swap_left (d l r : Word) (hd : d = 0 ∨ d = 1) :
    l ^^^ ((l ^^^ r) &&& (0 - d)) = if d = 0 then l else r := by
  rcases hd with rfl | rfl
  · rw [if_pos rfl]
    simp
  · rw [if_neg (by decide)]
    rw [show (0 : Word) - 1 = BitVec.allOnes 64 from by decide]
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The right output of the branchless swap. -/
theorem swap_right (d l r : Word) (hd : d = 0 ∨ d = 1) :
    r ^^^ ((l ^^^ r) &&& (0 - d)) = if d = 0 then r else l := by
  rcases hd with rfl | rfl
  · rw [if_pos rfl]
    simp
  · rw [if_neg (by decide)]
    rw [show (0 : Word) - 1 = BitVec.allOnes 64 from by decide]
    rw [show l ^^^ r = r ^^^ l from BitVec.xor_comm l r]
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The XOR/SLTIU equality test. -/
theorem eq_select (x y : Word) :
    (if BitVec.ult (x ^^^ y) 1 then (1 : Word) else 0)
      = (if x = y then (1 : Word) else 0) := by
  by_cases h : x = y
  · subst h
    rw [if_pos rfl, BitVec.xor_self]
    decide
  · have hnz : ¬ (BitVec.ult (x ^^^ y) 1 = true) := by
      intro hult
      apply h
      have h1 : (x ^^^ y).toNat < 1 := by
        simpa [BitVec.ult] using hult
      have hz : x ^^^ y = 0 := BitVec.eq_of_toNat_eq (by
        rw [show (0 : Word).toNat = 0 from rfl]
        omega)
      have h2 := congrArg (fun t => t ^^^ y) hz
      simpa [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] using h2
    rw [if_neg h, if_neg hnz]

/-! ## The mixing step as one instruction

`mix h x = h + x`, a single RV64 `ADD`. -/

/-- The instruction of one mixing step. -/
def mixInstr (rd rh rx : Reg) : Instr := .ADD rd rh rx

/-- Engine effect of one `ADD` mixing step. -/
theorem execInstrRF_mixInstr (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rh rx : Reg) :
    execInstrRF ro rwBase rf ws (mixInstr rd rh rx)
      = (rf.set rd (mix (rf.get rh) (rf.get rx)), ws) := by
  simp only [mixInstr, execInstrRF, aluSem, mix]

/-! ## Flat (swap-free) recurrence for the verifier

With `mix = +` every FORS/XMSS branchless swap collapses by
commutativity of addition, so the verifier reduces to a straight-line
word recurrence with a conditional only at the WOTS chain tops. -/

/-- `hW` is symmetric in its two message blocks (addition is
commutative), so the FORS/XMSS index-parity swap has no effect. -/
theorem hW_comm (pk adr l r : Word) : hW pk adr l r = hW pk adr r l := by
  simp only [hW, mix]; ac_rfl

/-- A FORS/XMSS index-parity swap collapses: since `hW` is symmetric in
its two message blocks, both branches of the parity `ite` are equal. -/
theorem fors_swap (b : Word) (pk adr l r : Word) :
    (if b = 0 then hW pk adr l r else hW pk adr r l) = hW pk adr l r := by
  rw [hW_comm pk adr r l, ite_self]

/-- The WOTS chain top as a branchless computation: `wi` plus the base word
`fW pkSeed adr 0 = fC + pkSeed + adr` masked by `d - 1` (all-ones when the
digit `d` is 0, zero when it is 1). -/
theorem chainTop_branchless (pk idx wi d : Word) (i : ℕ) (hd : d = 0 ∨ d = 1) :
    chainTopW pk idx i d wi
      = wi + ((fW pk (adrsW 0 idx (BitVec.ofNat 64 i) 0) 0) &&& (d - 1)) := by
  unfold chainTopW
  have hf : fW pk (adrsW 0 idx (BitVec.ofNat 64 i) 0) wi
      = (fW pk (adrsW 0 idx (BitVec.ofNat 64 i) 0) 0) + wi := by
    simp only [fW, mix]; ac_rfl
  rcases hd with rfl | rfl
  · rw [if_neg (by decide), hf]
    rw [show (0:Word) - 1 = BitVec.allOnes 64 from by decide, BitVec.and_allOnes,
      BitVec.add_comm]
  · rw [if_pos rfl, show (1:Word) - 1 = 0 from by decide]
    simp

/-! ## The verifier function

Registers: `a0`(x10) input pointer→result, `a1`(x11) pkSeed, `a2`(x12)
pkRoot, `a3`(x13) idxLeaf, `a4`(x14) FORS-pk then WOTS-leaf accumulator;
`t0`(x5) mb, `t1`(x6) work, `t2`(x7) hm/work, `t3`(x28) WOTS base const,
`t4`(x29) work, `t5`(x30) loads, `t6`(x31) work, `a5`(x15) WOTS base_i. -/

/-- The 21-word input list for a signature `s` and public key. -/
def inputWords (pkSeed pkRoot msgW : Word) (s : SigWords) : List Word :=
  [pkSeed, pkRoot, s.r, msgW, s.s0, s.a0, s.s1, s.a1] ++ List.ofFn s.w ++ [s.xa]

/-- One WOTS chain segment: load `w_i` (offset `o`), extract its digit from
`rsrc` at shift `sh`, and accumulate `w_i + base_i & (digit-1)` into `a4`,
using `base_i = t3 + i` materialized into `a5`. -/
def wotsChainInstrs (o : BitVec 12) (rsrc : Reg) (sh : BitVec 6) (i : BitVec 12) : List Instr :=
  [.LD .x30 .x10 o, .SRLI .x31 rsrc sh, .ANDI .x31 .x31 1, .ADDI .x31 .x31 (-1),
   .ADDI .x15 .x28 i, .AND .x31 .x15 .x31, .ADD .x30 .x30 .x31, .ADD .x14 .x14 .x30]

/-- The `load` block: load PK/signature words, compute the message digest
`hm` and its split (`idxLeaf`, `f0`, `f1`), recover the two FORS roots, and
accumulate the FORS public key into `x14`. -/
def loadInstrs : List Instr :=
  -- message digest hm = mC + r + pkSeed + pkRoot + msgW  (t2 = x7)
  [.LD .x11 .x10 0, .LD .x12 .x10 8, .LD .x5 .x10 16, .LD .x6 .x10 24,
   .LI .x7 mC, .ADD .x7 .x7 .x5, .ADD .x7 .x7 .x11, .ADD .x7 .x7 .x12,
   .ADD .x7 .x7 .x6,
  -- digest split: idxLeaf (x13), f0 (x28), f1 (x29)
   .ANDI .x13 .x7 1,
   .SRLI .x28 .x7 15, .ANDI .x28 .x28 1,
   .SRLI .x29 .x7 14, .ANDI .x29 .x29 1,
  -- FORS tree 0: leaf0 (x6), root0 (x7)
   .LD .x30 .x10 32, .LI .x6 fC, .ADD .x6 .x6 .x11, .LI .x7 adrsC,
   .ADD .x7 .x7 .x13, .ADDI .x7 .x7 3, .ADD .x7 .x7 .x28, .ADD .x6 .x6 .x7,
   .ADD .x6 .x6 .x30,
   .LD .x31 .x10 40, .LI .x7 hC, .ADD .x7 .x7 .x11, .LI .x5 adrsC,
   .ADD .x5 .x5 .x13, .ADDI .x5 .x5 4, .ADD .x7 .x7 .x5, .ADD .x7 .x7 .x6,
   .ADD .x7 .x7 .x31,
  -- forsPk accumulator (x14) := tlInit + root0
   .LI .x14 tC, .ADD .x14 .x14 .x11, .LI .x5 adrsC, .ADD .x5 .x5 .x13,
   .ADDI .x5 .x5 4, .ADD .x14 .x14 .x5, .ADD .x14 .x14 .x7,
  -- FORS tree 1: leaf1 (x6), root1 (x7)
   .LD .x30 .x10 48, .LI .x6 fC, .ADD .x6 .x6 .x11, .LI .x7 adrsC,
   .ADD .x7 .x7 .x13, .ADDI .x7 .x7 3, .ADD .x7 .x7 .x29, .ADDI .x7 .x7 2,
   .ADD .x6 .x6 .x7, .ADD .x6 .x6 .x30,
   .LD .x31 .x10 56, .LI .x7 hC, .ADD .x7 .x7 .x11, .LI .x5 adrsC,
   .ADD .x5 .x5 .x13, .ADDI .x5 .x5 5, .ADD .x7 .x7 .x5, .ADD .x7 .x7 .x6,
   .ADD .x7 .x7 .x31, .ADD .x14 .x14 .x7]

/-- The `wsetup` block: from the FORS public key in `x14`, form the WOTS+
committed byte `mb` (x5), the checksum `csum` (x7), the per-chain base
constant `fpConst` (x28), and reinitialize the WOTS+ leaf accumulator
`x14 := tlInit`. -/
def wsetupInstrs : List Instr :=
  -- WOTS committed byte mb (x5), digit-sum dsum (x6), checksum csum (x7)
  [.ANDI .x5 .x14 255,
   .LI .x6 0,
   .SRLI .x31 .x5 7, .ANDI .x31 .x31 1, .ADD .x6 .x6 .x31,
   .SRLI .x31 .x5 6, .ANDI .x31 .x31 1, .ADD .x6 .x6 .x31,
   .SRLI .x31 .x5 5, .ANDI .x31 .x31 1, .ADD .x6 .x6 .x31,
   .SRLI .x31 .x5 4, .ANDI .x31 .x31 1, .ADD .x6 .x6 .x31,
   .SRLI .x31 .x5 3, .ANDI .x31 .x31 1, .ADD .x6 .x6 .x31,
   .SRLI .x31 .x5 2, .ANDI .x31 .x31 1, .ADD .x6 .x6 .x31,
   .SRLI .x31 .x5 1, .ANDI .x31 .x31 1, .ADD .x6 .x6 .x31,
   .ANDI .x31 .x5 1, .ADD .x6 .x6 .x31,
   .LI .x7 8, .SUB .x7 .x7 .x6,
  -- WOTS base constant fpConst = fC + pkSeed + adrsC + idxLeaf (x28)
   .LI .x28 fC, .ADD .x28 .x28 .x11, .LI .x29 adrsC, .ADD .x28 .x28 .x29,
   .ADD .x28 .x28 .x13,
  -- WOTS leaf accumulator x14 := tlInit pkSeed (adrsW 1 idx 0 0)
   .LI .x14 tC, .ADD .x14 .x14 .x11, .LI .x30 adrsC, .ADD .x14 .x14 .x30,
   .ADD .x14 .x14 .x13, .ADDI .x14 .x14 1]

/-- The `wots` block: complete the twelve WOTS+ chains and compress with
`T_len` into the WOTS+ leaf public key (x14). -/
def wotsInstrs : List Instr :=
  wotsChainInstrs 64 .x5 7 0 ++ wotsChainInstrs 72 .x5 6 1 ++
  wotsChainInstrs 80 .x5 5 2 ++ wotsChainInstrs 88 .x5 4 3 ++
  wotsChainInstrs 96 .x5 3 4 ++ wotsChainInstrs 104 .x5 2 5 ++
  wotsChainInstrs 112 .x5 1 6 ++ wotsChainInstrs 120 .x5 0 7 ++
  wotsChainInstrs 128 .x7 3 8 ++ wotsChainInstrs 136 .x7 2 9 ++
  wotsChainInstrs 144 .x7 1 10 ++ wotsChainInstrs 152 .x7 0 11

/-- The `final` block: climb the single XMSS auth level to the candidate
root (x7) and compare against the public root, leaving `a0 = 1`/`0`. -/
def finalInstrs : List Instr :=
  [.LD .x30 .x10 160, .LI .x7 hC, .ADD .x7 .x7 .x11, .LI .x5 adrsC,
   .ADDI .x5 .x5 3, .ADD .x7 .x7 .x5, .ADD .x7 .x7 .x14, .ADD .x7 .x7 .x30,
   .XOR .x5 .x7 .x12, .SLTIU .x10 .x5 1]

open Stmt in
/-- The SLH-DSA verifier at the demonstration instance, in SAsm. -/
def slhVerifyFn (pkSeed pkRoot msgW : Word) (s : SigWords) : Fn where
  name := "slhVerify"
  region := ⟨inputBase, wordsBytes (inputWords pkSeed pkRoot msgW s)⟩
  pre := fun rf _ _ => rf.get .x10 = inputBase
  post := fun rf _ _ =>
    rf.get .x10 = (if demoVerifyWords pkSeed pkRoot msgW s then 1 else 0)
  body :=
    .block "load" loadInstrs ;;;
    .block "wsetup" wsetupInstrs ;;;
    .block "wots" wotsInstrs ;;;
    .block "final" finalInstrs

/-- The emitted machine program at address 0. -/
def slhVerify_program (pkSeed pkRoot msgW : Word) (s : SigWords) : Program :=
  (slhVerifyFn pkSeed pkRoot msgW s).body.flatten 0

/-- The verifier's emitted program is position-independent: the flattened
code is identical at address `0` and at `0x80000000`. -/
theorem slhVerify_position_independent (pkSeed pkRoot msgW : Word) (s : SigWords) :
    (slhVerifyFn pkSeed pkRoot msgW s).body.flatten 0
      = (slhVerifyFn pkSeed pkRoot msgW s).body.flatten 0x80000000 := by
  simp only [slhVerifyFn, loadInstrs, wsetupInstrs, wotsInstrs, wotsChainInstrs, finalInstrs]
  rfl

/-- The input region is well-formed whenever the input buffer fits the
machine's input arena. -/
theorem slhVerify_region_wf (pkSeed pkRoot msgW : Word) (s : SigWords) :
    (slhVerifyFn pkSeed pkRoot msgW s).region.wf := by
  apply slhInputRegion_wf
  rw [wordsBytes_length]
  simp only [inputWords, List.length_append, List.length_cons, List.length_nil,
    List.length_ofFn]
  omega

end SlhVerify
end EvmAsm.Rv64
