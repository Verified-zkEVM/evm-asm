/-
  EvmAsm.Codegen.Programs.BloomOrIntoSAsm

  Verified SAsm port of `bloom_or_into` (bead evm-asm-4ch8f.20): OR one
  256-byte bloom filter (`src`, a1) into another (`dst`, a0), in place, a
  dword at a time (32 iterations of `LD dst; LD src; OR; SD dst`).

  Post: the destination bloom becomes the **pointwise OR** of its original
  contents and the source — `dst[j] = dst₀[j] ||| src[j]` for every one of
  the 256 bytes.  This is the Ethereum block/receipt bloom accumulation
  (a dword `|||` is the byte-wise `|||` of its eight bytes).

  Structure: a top-tested `«while»` (the emitted `BEQ x5,x0 → exit; body;
  JAL back` shape) wrapped by a prologue block (`x5 := 32; x6 := dst;
  x7 := src`) and an epilogue block (`x10 := 0`, the return value).  The
  destination is the primary read-write region (read AND written — RMW);
  the source is the read-only `region`.

  Byte-identity: the structured flatten is pinned byte-for-byte against the
  emitted `bloomOrInto_prog` (Bloom.lean).  Spec-only module — no EEST A/B.
-/

import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace BloomOrIntoSAsm

/-! ## Pointwise-OR primitives -/

/-- Byte extraction commutes with `|||` (bitwise OR is per-byte). -/
theorem extractByte_or (a b : Word) (k : Nat) :
    extractByte (a ||| b) k = extractByte a k ||| extractByte b k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or]
  by_cases h : i < 8 <;> simp [h]

/-- Reading byte `k < 8` of the length-8 window `(L.drop a).take 8` is the
    total lookup `L.getD (a + k) 0`. -/
theorem getByteAt_dropTake (L : List (BitVec 8)) (a k : Nat) (hk : k < 8) :
    getByteAt ((L.drop a).take 8) k = L.getD (a + k) 0 := by
  unfold getByteAt
  by_cases hlt : k < ((L.drop a).take 8).length
  · rw [dif_pos hlt, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by
        simp only [List.length_take, List.length_drop] at hlt; omega),
      Option.getD_some]
  · rw [dif_neg hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      simp only [List.length_take, List.length_drop] at hlt ⊢; omega), Option.getD_none]

/-- The `k`-th output byte of the OR loop: original dst byte OR source byte. -/
def orByte (src orig : List (BitVec 8)) (k : Nat) : BitVec 8 :=
  orig.getD k 0 ||| src.getD k 0

/-- `dwordBytes` as a `map` of `extractByte` over `range 8`. -/
theorem dwordBytes_eq_map (v : Word) :
    dwordBytes v = (List.range 8).map (extractByte v) := by rfl

/-- The eight bytes of the stored dword `packBytes origCell ||| packBytes
    srcCell` (cell `i`) are exactly the pointwise ORs `orByte src orig
    (8*i + ·)`. -/
theorem dwordBytes_or_slice (src orig : List (BitVec 8)) (i : Nat) :
    dwordBytes (packBytes ((orig.drop (8 * i)).take 8)
        ||| packBytes ((src.drop (8 * i)).take 8))
      = (List.range 8).map (fun k => orByte src orig (8 * i + k)) := by
  rw [dwordBytes_eq_map]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [extractByte_or, extractByte_packBytes_total _ k hk, extractByte_packBytes_total _ k hk,
    getByteAt_dropTake _ _ _ hk, getByteAt_dropTake _ _ _ hk]
  rfl

/-! ## The OR loop window -/

/-- Loop window after `i` dwords OR'd: the first `8*i` bytes are the pointwise
    OR, the rest is the untouched tail of the original dst bloom. -/
def orWin (src orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (List.range (8 * i)).map (orByte src orig) ++ orig.drop (8 * i)

theorem orWin_zero (src orig : List (BitVec 8)) : orWin src orig 0 = orig := by
  simp [orWin]

theorem length_orWin (src orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 256) (hi : i ≤ 32) : (orWin src orig i).length = 256 := by
  simp only [orWin, List.length_append, List.length_map, List.length_range,
    List.length_drop, h]
  omega

/-- `List.range (8*(i+1))` splits after the first `8*i` entries into the eight
    cell indices `8*i + k`. -/
theorem map_orByte_range_succ (src orig : List (BitVec 8)) (i : Nat) :
    (List.range (8 * (i + 1))).map (orByte src orig)
      = (List.range (8 * i)).map (orByte src orig)
        ++ (List.range 8).map (fun k => orByte src orig (8 * i + k)) := by
  rw [show 8 * (i + 1) = 8 * i + 8 from by omega, List.range_add, List.map_append,
    List.map_map]
  rfl

/-- One dword step: splicing cell `i`'s stored dword advances the window from
    `i` to `i+1`. -/
theorem orWin_step (src orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 256) (hi : i < 32) :
    setBytes (orWin src orig i) (8 * i)
        (dwordBytes (packBytes ((orig.drop (8 * i)).take 8)
          ||| packBytes ((src.drop (8 * i)).take 8)))
      = orWin src orig (i + 1) := by
  have hpre : ((List.range (8 * i)).map (orByte src orig)).length = 8 * i := by simp
  have htk8 : ((orig.drop (8 * i)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, h]; omega
  -- A dword store at offset 0 of `orig.drop (8*i)` (abstracted over the stored
  -- word `V` so the split does not disturb the CELL that mentions `orig.drop`).
  have hsub : ∀ V : Word,
      setBytes (orig.drop (8 * i)) 0 (dwordBytes V)
        = dwordBytes V ++ (orig.drop (8 * i)).drop 8 := by
    intro V
    conv_lhs => rw [show orig.drop (8 * i)
        = (orig.drop (8 * i)).take 8 ++ (orig.drop (8 * i)).drop 8 from
        (List.take_append_drop 8 _).symm]
    rw [setBytes_append_left _ _ _ _ (by simp [htk8]), setBytes_dword_full _ _ htk8]
  simp only [orWin]
  rw [setBytes_append_right _ _ _ _ hpre.le, hpre, Nat.sub_self, hsub,
    dwordBytes_or_slice, List.drop_drop, ← List.append_assoc, ← map_orByte_range_succ,
    show 8 * i + 8 = 8 * (i + 1) from by omega]

/-- At `i = 32` the whole window is the pointwise OR of all 256 bytes. -/
theorem orWin_full (src orig : List (BitVec 8)) (h : orig.length = 256) :
    orWin src orig 32 = (List.range 256).map (orByte src orig) := by
  rw [orWin, show 8 * 32 = 256 from by norm_num, List.drop_eq_nil_of_le (by rw [h]),
    List.append_nil]

/-! ## The `bloom_or_into` SAsm function -/

/-- Prologue: `x5 := 32` (dword count), `x6 := dst` (a0), `x7 := src` (a1). -/
def proBlock : List Instr := [.LI .x5 (32 : Word), .MV .x6 .x10, .MV .x7 .x11]

/-- One dword OR step: load dst cell, load src cell, OR, store dst cell,
    advance both cursors by 8, decrement the count. -/
def orStepBlock : List Instr :=
  [.LD .x28 .x6 (0 : BitVec 12), .LD .x29 .x7 (0 : BitVec 12),
   .OR .x28 .x28 .x29, .SD .x6 .x28 (0 : BitVec 12),
   .ADDI .x6 .x6 (8 : BitVec 12), .ADDI .x7 .x7 (8 : BitVec 12),
   .ADDI .x5 .x5 (-1 : BitVec 12)]

/-- Epilogue: `x10 := 0` (the routine returns 0). -/
def epiBlock : List Instr := [.LI .x10 (0 : Word)]

/-- Loop invariant after `i` dwords: cursors at `+8*i`, count `32-i`, and the
    dst working set is the `i`-dword OR window. -/
def bloomOrInv (src dst : Word) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x5 = BitVec.ofNat 64 (32 - i) ∧
    rf.get .x6 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x7 = src + BitVec.ofNat 64 (8 * i) ∧
    i ≤ 32 ∧ srcBytes.length = 256 ∧ orig.length = 256 ∧
    src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) ∧
    ws = orWin srcBytes orig i

/-- `bloom_or_into` body: prologue ; the 32-iteration dword OR loop ; epilogue. -/
def bloomOrBody (src dst : Word) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "pro" proBlock ;;;
  .«while» "loop" (.bne .x5 .x0) 32 (bloomOrInv src dst srcBytes orig)
    (.block "step" orStepBlock) ;;;
  .block "epi" epiBlock

/-- `bloom_or_into` as a verified SAsm `Fn`: src is the read-only region, dst
    the read-write region (RMW).  Post: dst = pointwise OR of dst₀ and src. -/
def bloomOrIntoFn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "bloomOrInto"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 256⟩
  pre := fun rf ws _ =>
    rf.get .x10 = dst ∧ rf.get .x11 = src ∧
    ws = orig ∧ orig.length = 256 ∧ srcBytes.length = 256 ∧
    src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat)
  post := fun rf ws _ =>
    rf.get .x10 = 0 ∧ ws = (List.range 256).map (orByte srcBytes orig)
  body := bloomOrBody src dst srcBytes orig

/-! ## Byte-identity to the emitted routine -/

-- The structured flatten is exactly `bloomOrInto_prog` minus the trailing
-- `ret`: prologue (3) ++ while (guard + 7-instr body + JAL back = 9) ++
-- epilogue (1) = 13 instrs; `++ [ret]` = the 14-instr emitted routine.
#guard (bloomOrBody 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0]
    = bloomOrInto_prog

-- Position independence: no PC-relative instructions leak an absolute address.
#guard (bloomOrBody 0 0 [] []).flatten 0
    = (bloomOrBody 0 0 [] []).flatten 0x80000000

#guard bloomOrInto_prog.length = 14

end BloomOrIntoSAsm

end EvmAsm.Codegen
