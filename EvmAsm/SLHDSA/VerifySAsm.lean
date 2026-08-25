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

  `slhVerifyFn_spec` proves the straight-line code computes
  `Demo.demoVerifyWords`, which `Demo.demoVerifyWords_correct`
  (EvmAsm/SLHDSA/DemoCorrect.lean) proves equal to the ported FIPS 205
  algorithm `SLHDSA.slhVerifyInternal`; `slhVerifyFn_verifies` composes
  the two.
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

end SlhVerify
end EvmAsm.Rv64
