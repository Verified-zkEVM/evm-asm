/-
  EvmAsm.Evm64.Push.ImmediateCompose

  Completes the PUSH2..32 stack spec (`evm_push_stack_spec_within`): a single
  unconditional top-level Hoare triple for `evm_push n` at any width
  `1 ≤ n ≤ 32`, lifting the family from proof tier `.partly` (zero-immediate
  only, via `evm_push_zero_slot_full_stack_spec_within`) to `.proven`.

  Strategy (orthogonal to the existing single-cell `evm_push_one_byte_spec_within`):
  model BOTH the EVM code immediate source and the freshly-allocated 32-byte
  stack slot as byte-addressable `bytesRegion`s (`Rv64/MemRegion.lean`). This
  sidesteps the symbolic-limb case split — with symbolic `n`, immediate byte `i`
  lands in limb `(n-1-i)/8`, which is not a concrete value, so the four explicit
  limb cells cannot be selected per step. A uniform `bytesRegion` byte write
  (`bytesRegion_sb_within`) handles every byte the same way.

  Pipeline:
    * Section A — region read/write with the offset in the LBU/SB *immediate*
      (the PUSH program keeps `x10`/`x12` fixed and varies the immediate), the
      addressing the `..._within` region specs (pointer-advanced, immediate 0)
      do not provide.
    * Section B — `pushSlotBytes`, the 32-byte accumulator, and the
      `bytesRegion ↔ evmWordIs` bridge with the final fold to `pushImmediateWord`.
    * Section C — the inductive `n`-byte copy spec under `evm_push_code`.
    * Section D — the top-level `evm_push_stack_spec_within`.
-/

import EvmAsm.Evm64.Push.Spec
import EvmAsm.Rv64.MemRegionStore

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section A — region byte read/write addressed by the LBU/SB immediate
-- ============================================================================

/-- `LBU rd rs1 (ofNat j)` with `rs1 ↦ regionBase` reads byte `j` of the region.
    Immediate-offset analogue of `bytesRegion_lbu_within` (which keeps the
    immediate `0` and pre-advances the pointer to `regionBase + j`); the PUSH
    program instead keeps `x10 = codePtr` fixed and varies the immediate. -/
theorem bytesRegion_lbu_imm_within (rd rs1 : Reg) (regionBase vOld : Word) (base : Word)
    (bs : List (BitVec 8)) (j : Nat) (hrd : rd ≠ .x0)
    (halign : regionBase.toNat % 8 = 0) (hj : j < bs.length) (hj2048 : j < 2048)
    (hover : regionBase.toNat + j < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 (BitVec.ofNat 12 j)))
      ((rs1 ↦ᵣ regionBase) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ regionBase) **
       (rd ↦ᵣ ((bs[j]'hj).zeroExtend 64)) ** bytesRegion regionBase bs) := by
  have hse : signExtend12 (BitVec.ofNat 12 j) = BitVec.ofNat 64 j :=
    signExtend12_ofNat_small hj2048
  have hptr : regionBase + signExtend12 (BitVec.ofNat 12 j) = regionBase + BitVec.ofNat 64 j := by
    rw [hse]
  have hq : 8 * (j / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs (j / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (j / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (j / 8))).take 8) with hwv
  have halign' :
      alignToDword (regionBase + signExtend12 (BitVec.ofNat 12 j)) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess (regionBase + signExtend12 (BitVec.ofNat 12 j)) = true := by
    rw [hptr]; exact hvalid
  have lbu := generic_lbu_spec_within rd rs1 regionBase vOld (BitVec.ofNat 12 j) base
    dwordAddr wordVal hrd halign' hvalid'
  have hbyte : extractByte wordVal (byteOffset (regionBase + signExtend12 (BitVec.ofNat 12 j)))
      = bs[j]'hj := by
    rw [hptr, byteOffset_add_ofNat_of_aligned halign hover, hwv,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

/-- `SB rs1 rs2 (ofNat j)` with `rs1 ↦ regionBase` writes the low byte of `rs2`
    into byte `j` of the region. Immediate-offset analogue of
    `bytesRegion_sb_within`. -/
theorem bytesRegion_sb_imm_within (rs1 rs2 : Reg) (regionBase v_data : Word) (base : Word)
    (bs : List (BitVec 8)) (j : Nat)
    (halign : regionBase.toNat % 8 = 0) (hj : j < bs.length) (hj2048 : j < 2048)
    (hover : regionBase.toNat + j < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 (BitVec.ofNat 12 j)))
      ((rs1 ↦ᵣ regionBase) ** (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ regionBase) ** (rs2 ↦ᵣ v_data) **
       bytesRegion regionBase (bs.set j (v_data.truncate 8))) := by
  have hse : signExtend12 (BitVec.ofNat 12 j) = BitVec.ofNat 64 j :=
    signExtend12_ofNat_small hj2048
  have hptr : regionBase + signExtend12 (BitVec.ofNat 12 j) = regionBase + BitVec.ofNat 64 j := by
    rw [hse]
  have hr8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hj_eq : 8 * (j / 8) + j % 8 = j := Nat.div_add_mod j 8
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegion_dword_at_set regionBase bs (j / 8) (j % 8) (v_data.truncate 8) hr8 (by omega)
  rw [hj_eq] at heqset
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (j / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (j / 8))).take 8) with hwv
  have halign' :
      alignToDword (regionBase + signExtend12 (BitVec.ofNat 12 j)) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess (regionBase + signExtend12 (BitVec.ofNat 12 j)) = true := by
    rw [hptr]; exact hvalid
  have sb := generic_sb_spec_within rs1 rs2 regionBase v_data (BitVec.ofNat 12 j) base
    dwordAddr wordVal halign' hvalid'
  have hbo : byteOffset (regionBase + signExtend12 (BitVec.ofNat 12 j)) = j % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : j % 8 < ((bs.drop (8 * (j / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, packBytes_set _ (j % 8) (v_data.truncate 8) hr8 hchunk_len] at sb
  rw [heq, heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sb)

-- ============================================================================
-- Section B — the 32-byte slot accumulator and the bytes ↔ EvmWord bridge
-- ============================================================================

/-- The 32-byte stack-slot contents after the first `k` PUSH immediate-byte
    copies: start all-zero, then for each `i < k` place `byteAt i` at the
    big-endian destination position `pushByteDstOffset n i = n-1-i`. -/
def pushSlotBytes (n : Nat) (byteAt : Nat → BitVec 8) : Nat → List (BitVec 8)
  | 0 => List.replicate 32 0
  | k + 1 => (pushSlotBytes n byteAt k).set (pushByteDstOffset n k) (byteAt k)

@[simp] theorem pushSlotBytes_zero (n : Nat) (byteAt : Nat → BitVec 8) :
    pushSlotBytes n byteAt 0 = List.replicate 32 0 := rfl

theorem pushSlotBytes_succ (n : Nat) (byteAt : Nat → BitVec 8) (k : Nat) :
    pushSlotBytes n byteAt (k + 1)
      = (pushSlotBytes n byteAt k).set (pushByteDstOffset n k) (byteAt k) := rfl

theorem pushSlotBytes_length (n : Nat) (byteAt : Nat → BitVec 8) (k : Nat) :
    (pushSlotBytes n byteAt k).length = 32 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pushSlotBytes_succ, List.length_set, ih]

/-- Partial fold of `pushImmediateLimb` over the first `k` immediate bytes. At
    `k = n` it is `pushImmediateLimb n byteAt limb` definitionally. -/
def pushImmediatePartialLimb (n : Nat) (byteAt : Nat → BitVec 8) (limb k : Nat) : Word :=
  (List.range k).foldl
    (fun acc i =>
      let dst := pushByteDstOffset n i
      if dst / 8 = limb then replaceByte acc (dst % 8) (byteAt i) else acc)
    (0 : Word)

theorem pushImmediatePartialLimb_full (n : Nat) (byteAt : Nat → BitVec 8) (limb : Nat) :
    pushImmediatePartialLimb n byteAt limb n = pushImmediateLimb n byteAt limb := rfl

theorem pushImmediatePartialLimb_succ (n : Nat) (byteAt : Nat → BitVec 8) (limb k : Nat) :
    pushImmediatePartialLimb n byteAt limb (k + 1)
      = (if pushByteDstOffset n k / 8 = limb then
          replaceByte (pushImmediatePartialLimb n byteAt limb k)
            (pushByteDstOffset n k % 8) (byteAt k)
         else pushImmediatePartialLimb n byteAt limb k) := by
  unfold pushImmediatePartialLimb
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Chunk-localized `set`: writing byte `p` into `l` only affects the dword
    chunk `p / 8`, at byte `p % 8`. -/
theorem drop_take_set_chunk {α : Type _} (l : List α) (p m : Nat) (b : α)
    (hm : 8 * m + 8 ≤ l.length) :
    List.take 8 (List.drop (8 * m) (l.set p b))
      = if p / 8 = m then (List.take 8 (List.drop (8 * m) l)).set (p % 8) b
        else List.take 8 (List.drop (8 * m) l) := by
  rw [List.drop_set]
  by_cases hlt : p < 8 * m
  · rw [if_pos hlt, if_neg (show ¬ (p / 8 = m) by omega)]
  · rw [if_neg hlt, List.take_set]
    by_cases hpm : p / 8 = m
    · rw [if_pos hpm, show p - 8 * m = p % 8 by omega]
    · rw [if_neg hpm,
        List.set_eq_of_length_le (by rw [List.length_take, List.length_drop]; omega)]

theorem getByteAt_replicate_zero (m j : Nat) :
    getByteAt (List.replicate m (0 : BitVec 8)) j = 0 := by
  unfold getByteAt
  split <;> simp [List.getElem_replicate]

theorem packBytes_replicate_zero (m : Nat) :
    packBytes (List.replicate m (0 : BitVec 8)) = 0 := by
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes_total _ j hj, getByteAt_replicate_zero]
  simp [extractByte]

/-- **Per-limb bridge.** The `limb`-th dword chunk of the slot bytes after `k`
    copies packs to the partial immediate limb. -/
theorem packBytes_slice_pushSlotBytes (n : Nat) (byteAt : Nat → BitVec 8)
    (hn : n ≤ 32) (limb : Nat) (hlimb : limb < 4) (k : Nat) (hk : k ≤ n) :
    packBytes (List.take 8 (List.drop (8 * limb) (pushSlotBytes n byteAt k)))
      = pushImmediatePartialLimb n byteAt limb k := by
  induction k with
  | zero =>
    rw [pushSlotBytes_zero, List.drop_replicate, List.take_replicate,
        show min 8 (32 - 8 * limb) = 8 by omega, packBytes_replicate_zero]
    rfl
  | succ k ih =>
    have hk' : k ≤ n := by omega
    have hp : pushByteDstOffset n k < 32 := pushByteDstOffset_lt_32_of_lt hn (by omega)
    have hlen : (pushSlotBytes n byteAt k).length = 32 := pushSlotBytes_length n byteAt k
    rw [pushSlotBytes_succ, pushImmediatePartialLimb_succ,
        drop_take_set_chunk _ _ _ _ (by rw [hlen]; omega)]
    by_cases hpm : pushByteDstOffset n k / 8 = limb
    · rw [if_pos hpm, if_pos hpm, ← ih hk',
          packBytes_set _ _ _ (by omega)
            (by rw [List.length_take, List.length_drop, hlen]; omega)]
    · rw [if_neg hpm, if_neg hpm, ih hk']

/-- **Region ↔ word bridge.** A 32-byte region folds to `evmWordIs` of any
    `EvmWord` whose four limbs pack the four dword chunks. -/
theorem bytesRegion_eq_evmWordIs_of_limbs (nsp : Word) (bs : List (BitVec 8)) (v : EvmWord)
    (hlen : bs.length = 32)
    (h0 : v.getLimbN 0 = packBytes (List.take 8 (List.drop (8 * 0) bs)))
    (h1 : v.getLimbN 1 = packBytes (List.take 8 (List.drop (8 * 1) bs)))
    (h2 : v.getLimbN 2 = packBytes (List.take 8 (List.drop (8 * 2) bs)))
    (h3 : v.getLimbN 3 = packBytes (List.take 8 (List.drop (8 * 3) bs))) :
    bytesRegion nsp bs = evmWordIs nsp v := by
  have hne : bs ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have hne1 : List.drop 8 bs ≠ [] := by
    intro h; have := List.length_eq_zero_iff.mpr h; rw [List.length_drop, hlen] at this; omega
  have hne2 : List.drop 8 (List.drop 8 bs) ≠ [] := by
    intro h; have := List.length_eq_zero_iff.mpr h
    rw [List.length_drop, List.length_drop, hlen] at this; omega
  have hne3 : List.drop 8 (List.drop 8 (List.drop 8 bs)) ≠ [] := by
    intro h; have := List.length_eq_zero_iff.mpr h
    rw [List.length_drop, List.length_drop, List.length_drop, hlen] at this; omega
  rw [evmWordIs_sp_limbs_eq nsp v _ _ _ _ h0 h1 h2 h3]
  rw [bytesRegion_eq_cons nsp bs hne, bytesRegion_eq_cons (nsp + 8) _ hne1,
      bytesRegion_eq_cons (nsp + 8 + 8) _ hne2, bytesRegion_eq_cons (nsp + 8 + 8 + 8) _ hne3]
  rw [show List.drop 8 (List.drop 8 (List.drop 8 (List.drop 8 bs))) = []
        from List.drop_eq_nil_of_le (by simp only [List.length_drop, hlen]; omega)]
  rw [bytesRegion_nil, sepConj_emp_right']
  simp only [List.drop_drop, Nat.mul_zero, Nat.mul_one, List.drop_zero,
             show (8 : Nat) + 8 = 16 from rfl, show (8 : Nat) + 8 + 8 = 24 from rfl,
             show (8 : Nat) * 2 = 16 from rfl, show (8 : Nat) * 3 = 24 from rfl]
  rw [show nsp + 8 + 8 = nsp + 16 by bv_omega, show nsp + 16 + 8 = nsp + 24 by bv_omega]

-- ============================================================================
-- Section C — the inductive n-byte copy chain
-- ============================================================================

/-- The value left in `x7` after the first `k` PUSH byte copies: the initial
    junk `v7` if no byte has been copied, otherwise the most recent immediate. -/
def pushX7After (codeBytes : List (BitVec 8)) (v7 : Word) : Nat → Word
  | 0 => v7
  | k + 1 => (getByteAt codeBytes (1 + k)).zeroExtend 64

private theorem trunc8_zext64 (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 b) = b := by
  simp [BitVec.truncate_eq_setWidth]

private theorem getByteAt_of_lt {l : List (BitVec 8)} {i : Nat} (h : i < l.length) :
    getByteAt l i = l[i] := by rw [getByteAt, dif_pos h]

/-- **One PUSH byte copy** (`LBU x7 x10 (1+k) ;; SB x12 x7 (n-1-k)`): read
    immediate byte `1+k` from the code region into `x7`, store its low byte into
    destination position `n-1-k` of the slot region. -/
theorem push_byte_block_spec
    (n k : Nat) (hn : n ≤ 32) (hk : k < n)
    (codePtr nsp v7 : Word) (blockBase : Word)
    (codeBytes bs : List (BitVec 8))
    (hcodealign : codePtr.toNat % 8 = 0) (hnspalign : nsp.toNat % 8 = 0)
    (hcodelen : n + 1 ≤ codeBytes.length) (hbslen : bs.length = 32)
    (hcodeover : codePtr.toNat + n + 1 < 2 ^ 64) (hnspover : nsp.toNat + 32 < 2 ^ 64)
    (hcodevalid : isValidByteAccess (codePtr + BitVec.ofNat 64 (1 + k)) = true)
    (hnspvalid : isValidByteAccess (nsp + BitVec.ofNat 64 (pushByteDstOffset n k)) = true) :
    cpsTripleWithin 2 blockBase (blockBase + 8)
      (CodeReq.ofProg blockBase (push_one_byte n k))
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ v7) **
       bytesRegion codePtr codeBytes ** bytesRegion nsp bs)
      ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ nsp) **
       (.x7 ↦ᵣ ((getByteAt codeBytes (1 + k)).zeroExtend 64)) **
       bytesRegion codePtr codeBytes **
       bytesRegion nsp (bs.set (pushByteDstOffset n k) (getByteAt codeBytes (1 + k)))) := by
  have hsrc : (1 + k) < codeBytes.length := by omega
  have hdst : pushByteDstOffset n k < bs.length := by
    rw [hbslen]; exact pushByteDstOffset_lt_32_of_lt hn hk
  -- LBU reads code byte (1+k) into x7, framed against the destination region.
  have lbu := bytesRegion_lbu_imm_within .x7 .x10 codePtr v7 blockBase codeBytes (1 + k)
    (by decide) hcodealign hsrc (by omega) (by omega) hcodevalid
  rw [← getByteAt_of_lt hsrc] at lbu
  have lbuF := cpsTripleWithin_frameR ((.x12 ↦ᵣ nsp) ** bytesRegion nsp bs)
    (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) lbu
  -- SB stores x7's low byte into slot byte (n-1-k), framed against the code region.
  have sb := bytesRegion_sb_imm_within .x12 .x7 nsp ((getByteAt codeBytes (1 + k)).zeroExtend 64)
    (blockBase + 4) bs (pushByteDstOffset n k) hnspalign hdst
    (by have := pushByteDstOffset_lt_32_of_lt hn hk; omega) (by
      have := pushByteDstOffset_lt_32_of_lt hn hk; omega) hnspvalid
  rw [trunc8_zext64] at sb
  have sbF := cpsTripleWithin_frameR ((.x10 ↦ᵣ codePtr) ** bytesRegion codePtr codeBytes)
    (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) sb
  -- Compose LBU then SB; rewrite the singleton-union code into `ofProg`.
  have hd : (CodeReq.singleton blockBase (.LBU .x7 .x10 (BitVec.ofNat 12 (1 + k)))).Disjoint
      (CodeReq.singleton (blockBase + 4) (.SB .x12 .x7 (BitVec.ofNat 12 (pushByteDstOffset n k)))) := by
    crDisjoint
  have hseq := cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ h => by xperm_hyp h) lbuF)
    sbF
  rw [push_one_byte_code_eq_ofProg blockBase (BitVec.ofNat 12 (1 + k))
        (BitVec.ofNat 12 (pushByteDstOffset n k)),
      show (blockBase + 4 + 4 : Word) = blockBase + 8 by bv_omega] at hseq
  exact cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => by xperm_hyp h) hseq

/-- **Unrolled PUSH immediate-copy chain.** Running the first `k` of `evm_push n`'s
    byte copies (the slice `push_bytes n k` at `pb`) transforms the zero-filled
    slot region into `pushSlotBytes n byteAt k`, leaving the code region intact. -/
theorem evm_push_bytes_region_spec
    (n : Nat) (hn : n ≤ 32) (codePtr nsp v7 pb : Word)
    (codeBytes : List (BitVec 8)) (byteAt : Nat → BitVec 8)
    (hcodealign : codePtr.toNat % 8 = 0) (hnspalign : nsp.toNat % 8 = 0)
    (hcodelen : n + 1 ≤ codeBytes.length)
    (hcodeover : codePtr.toNat + n + 1 < 2 ^ 64) (hnspover : nsp.toNat + 32 < 2 ^ 64)
    (hpbover : pb.toNat + 8 * n < 2 ^ 64)
    (hcodevalid : ∀ j, j ≤ n → isValidByteAccess (codePtr + BitVec.ofNat 64 j) = true)
    (hnspvalid : ∀ j, j < 32 → isValidByteAccess (nsp + BitVec.ofNat 64 j) = true)
    (hbyteAt : ∀ i, i < n → byteAt i = getByteAt codeBytes (1 + i)) :
    ∀ (k : Nat), k ≤ n →
      cpsTripleWithin (2 * k) pb (pb + BitVec.ofNat 64 (8 * k))
        (CodeReq.ofProg pb (push_bytes n k))
        ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ v7) **
         bytesRegion codePtr codeBytes ** bytesRegion nsp (pushSlotBytes n byteAt 0))
        ((.x10 ↦ᵣ codePtr) ** (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ pushX7After codeBytes v7 k) **
         bytesRegion codePtr codeBytes ** bytesRegion nsp (pushSlotBytes n byteAt k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.mul_zero, pushX7After]
    rw [show pb + BitVec.ofNat 64 0 = pb from by bv_omega, push_bytes, prog_skip,
        CodeReq.ofProg_nil]
    exact cpsTripleWithin_refl (fun _ h => h)
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hIH := ih (by omega)
    have block := push_byte_block_spec n k hn hkn codePtr nsp
      (pushX7After codeBytes v7 k) (pb + BitVec.ofNat 64 (8 * k))
      codeBytes (pushSlotBytes n byteAt k) hcodealign hnspalign hcodelen
      (pushSlotBytes_length n byteAt k) hcodeover hnspover
      (hcodevalid (1 + k) (by omega))
      (hnspvalid (pushByteDstOffset n k) (pushByteDstOffset_lt_32_of_lt hn hkn))
    have hd : (CodeReq.ofProg pb (push_bytes n k)).Disjoint
        (CodeReq.ofProg (pb + BitVec.ofNat 64 (8 * k)) (push_one_byte n k)) := by
      refine CodeReq.ofProg_disjoint_range_len pb (push_bytes n k) (2 * k)
        (pb + BitVec.ofNat 64 (8 * k)) (push_one_byte n k) 2
        (push_bytes_length n k) (push_one_byte_length n k) ?_
      intro k1 k2 hk1 hk2
      have : pb.toNat + 8 * k + 4 < 2 ^ 64 := by omega
      bv_omega
    have hseq := cpsTripleWithin_seq hd hIH block
    have hbase : pb + BitVec.ofNat 64 (8 * k)
        = pb + BitVec.ofNat 64 (4 * (push_bytes n k).length) := by
      rw [push_bytes_length, show 4 * (2 * k) = 8 * k from by omega]
    have hcr : (CodeReq.ofProg pb (push_bytes n k)).union
            (CodeReq.ofProg (pb + BitVec.ofNat 64 (8 * k)) (push_one_byte n k))
          = CodeReq.ofProg pb (push_bytes n (k + 1)) := by
      rw [hbase, ← CodeReq.ofProg_append]; rfl
    rw [← hcr, show 2 * (k + 1) = 2 * k + 2 by omega, pushSlotBytes_succ, hbyteAt k hkn,
        show pb + BitVec.ofNat 64 (8 * (k + 1)) = pb + BitVec.ofNat 64 (8 * k) + 8 by bv_omega,
        show pushX7After codeBytes v7 (k + 1) = (getByteAt codeBytes (1 + k)).zeroExtend 64 from rfl]
    exact hseq

-- ============================================================================
-- Section D — the top-level PUSH2..32 stack spec
-- ============================================================================

/-- The zero-filled slot region is the EVM word `0`. -/
theorem pushSlotBytes_zero_region (nsp : Word) (n : Nat) (byteAt : Nat → BitVec 8) :
    bytesRegion nsp (pushSlotBytes n byteAt 0) = evmWordIs nsp (0 : EvmWord) := by
  rw [pushSlotBytes_zero]
  refine bytesRegion_eq_evmWordIs_of_limbs nsp (List.replicate 32 0) 0 (by simp) ?_ ?_ ?_ ?_ <;>
    rw [EvmWord.getLimbN_zero, List.drop_replicate, List.take_replicate, packBytes_replicate_zero]

/-- The fully-copied slot region is the EVM word assembled from the immediate
    bytes (`pushImmediateWord`). -/
theorem pushSlotBytes_full_region (nsp : Word) (n : Nat) (hn : n ≤ 32)
    (byteAt : Nat → BitVec 8) :
    bytesRegion nsp (pushSlotBytes n byteAt n) = evmWordIs nsp (pushImmediateWord n byteAt) := by
  refine bytesRegion_eq_evmWordIs_of_limbs nsp (pushSlotBytes n byteAt n)
    (pushImmediateWord n byteAt) (pushSlotBytes_length n byteAt n) ?_ ?_ ?_ ?_
  · rw [pushImmediateWord_getLimbN_0,
        packBytes_slice_pushSlotBytes n byteAt hn 0 (by decide) n (le_refl n),
        pushImmediatePartialLimb_full]
  · rw [pushImmediateWord_getLimbN_1,
        packBytes_slice_pushSlotBytes n byteAt hn 1 (by decide) n (le_refl n),
        pushImmediatePartialLimb_full]
  · rw [pushImmediateWord_getLimbN_2,
        packBytes_slice_pushSlotBytes n byteAt hn 2 (by decide) n (le_refl n),
        pushImmediatePartialLimb_full]
  · rw [pushImmediateWord_getLimbN_3,
        packBytes_slice_pushSlotBytes n byteAt hn 3 (by decide) n (le_refl n),
        pushImmediatePartialLimb_full]

/-- `evm_push n` after its 5-instruction zero-fill prefix is exactly the
    `n`-byte copy chain. -/
theorem evm_push_drop_5 (n : Nat) : (evm_push n : List Instr).drop 5 = push_bytes n n := by
  unfold evm_push ADDI SD single seq
  rfl

/-- **PUSH2..32 — complete stack spec.** `evm_push n` (`1 ≤ n ≤ 32`) pushes the
    256-bit big-endian immediate `pushImmediateWord n byteAt` (its `n` bytes read
    from the EVM code region at `codePtr+1 .. codePtr+n`) onto the EVM stack. No
    input-domain restriction: the precondition only fixes the memory/code layout
    and alignment, so this is a `proven`-tier witness for the whole family. -/
theorem evm_push_stack_spec_within
    (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 32)
    (sp codePtr v7 d0 d1 d2 d3 : Word) (base : Word) (rest : List EvmWord)
    (codeBytes : List (BitVec 8)) (byteAt : Nat → BitVec 8)
    (hcodealign : codePtr.toNat % 8 = 0)
    (hcodelen : n + 1 ≤ codeBytes.length)
    (hcodeover : codePtr.toNat + n + 1 < 2 ^ 64)
    (hnspalign : (sp + signExtend12 ((-32 : BitVec 12))).toNat % 8 = 0)
    (hnspover : (sp + signExtend12 ((-32 : BitVec 12))).toNat + 32 < 2 ^ 64)
    (hbaseover : (base + (20 : Word)).toNat + 8 * n < 2 ^ 64)
    (hcodevalid : ∀ j, j ≤ n → isValidByteAccess (codePtr + BitVec.ofNat 64 j) = true)
    (hnspvalid : ∀ j, j < 32 →
      isValidByteAccess ((sp + signExtend12 ((-32 : BitVec 12))) + BitVec.ofNat 64 j) = true)
    (hbyteAt : ∀ i, i < n → byteAt i = getByteAt codeBytes (1 + i)) :
    let nsp := sp + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin (5 + 2 * n) base (base + BitVec.ofNat 64 (4 * (5 + 2 * n)))
      (evm_push_code base n)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ codePtr) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) **
       ((nsp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((nsp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((nsp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((nsp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       bytesRegion codePtr codeBytes ** evmStackIs sp rest)
      ((.x12 ↦ᵣ nsp) ** (.x10 ↦ᵣ codePtr) ** (.x7 ↦ᵣ pushX7After codeBytes v7 n) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion codePtr codeBytes **
       evmStackIs nsp (pushImmediateWord n byteAt :: rest)) := by
  intro nsp
  -- Prefix: allocate + zero-fill the slot.
  have hPrefix := evm_push_zero_slot_full_stack_spec_within n hn sp d0 d1 d2 d3 base rest
  have hPrefixF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ codePtr) ** (.x7 ↦ᵣ v7) ** bytesRegion codePtr codeBytes)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))
    hPrefix
  -- Chain: copy the n immediate bytes into the slot region.
  have hChain := evm_push_bytes_region_spec n hn codePtr nsp v7 (base + 20) codeBytes byteAt
    hcodealign hnspalign hcodelen hcodeover hnspover hbaseover hcodevalid hnspvalid hbyteAt n
    (le_refl n)
  have hChainCode := cpsTripleWithin_extend_code (cr' := evm_push_code base n)
    (hmono := by
      refine CodeReq.ofProg_mono_sub base (base + 20) (evm_push n) (push_bytes n n) 5
        (by bv_omega) ?_ ?_ ?_
      · rw [evm_push_drop_5]; exact List.take_length
      · rw [push_bytes_length, evm_push_length]
      · rw [evm_push_length]; omega)
    (h := hChain)
  have hChainF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** evmStackIs (nsp + 32) rest)
    (pcFree_sepConj pcFree_regIs pcFree_evmStackIs)
    hChainCode
  -- Compose prefix then chain.
  have hSeq := cpsTripleWithin_seq_same_cr hPrefixF
    (cpsTripleWithin_weaken
      (fun _ hp => by
        rw [evmStackIs_cons, ← pushSlotBytes_zero_region nsp n byteAt] at hp
        xperm_hyp hp)
      (fun _ hp => hp)
      hChainF)
  -- Normalize step count and exit address; fold the final slot back into the stack.
  rw [show base + 20 + BitVec.ofNat 64 (8 * n) = base + BitVec.ofNat 64 (4 * (5 + 2 * n)) by bv_omega]
    at hSeq
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => ?_) hSeq
  rw [pushSlotBytes_full_region nsp n hn byteAt] at hp
  rw [evmStackIs_cons]
  xperm_hyp hp

-- Sanity: the word `evm_push_stack_spec_within` pushes is the big-endian reading
-- of the immediate bytes (byte `i` of the immediate is `byteAt i`).
example : pushImmediateWord 2 (fun i => if i = 0 then 0xAB else 0xCD) = (0xABCD : EvmWord) := by
  decide
example : pushImmediateWord 1 (fun _ => 0xFF) = (0xFF : EvmWord) := by decide
example : pushImmediateWord 32 (fun _ => 0xFF) = (0 : EvmWord) - 1 := by decide

end EvmAsm.Evm64
