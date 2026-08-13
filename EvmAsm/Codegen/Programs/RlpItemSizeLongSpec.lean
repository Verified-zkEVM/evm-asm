/-
  EvmAsm.Codegen.Programs.RlpItemSizeLongSpec

  **`rlp_item_size`, the two long forms** (GH #10780) — the arms
  `RlpSpliceHelperSpec.SpanForm` excludes.

  `RlpSpliceHelperSpec.lean` proves the three short arms of the same 35-instruction
  routine (single byte, short string `0x80..0xB7`, short list `0xC0..0xF7`) and its
  `SpanForm` predicate then rules out `0xB8..0xBF` and `0xF8..0xFF`, which is what
  makes the unified dispatch `.conditional`. This module supplies the two missing
  machine arms, in the same per-arm pinned-triple shape:

  * `rlp_item_size_long_string_pinned_spec_within` — `0xB8 ≤ prefix < 0xC0`
  * `rlp_item_size_long_list_pinned_spec_within`   — `0xF8 ≤ prefix`

  It lives in its own module rather than in `RlpSpliceHelperSpec.lean` purely for the
  1500-line file cap (`scripts/check-file-size.sh`) — the same split
  `RlpEncodeListPrefixLong2Spec.lean`/`Long3Spec.lean` made for the sibling routine.

  ## ⭐ The length loop is cited, not unrolled

  Both long forms fall into a shared tail (idx22–34) that reads `lenOfLen` big-endian
  length bytes into `x28` and returns `1 + lenOfLen + x28`. `lenOfLen` ranges over
  `1..8`, so the loop cannot be unrolled the way a fixed-width arm can. It does not
  have to be: `EvmAsm.Rv64.RLP.risLenLoop` verifies idx25–31 whole at a symbolic trip
  count `n` in `7 * n + 1` steps, accumulating
  `x28 = BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))`.
  Both arms instantiate it at `pre := []`, `si := 1`, `n := lenOfLen`, so the loop
  costs about fifteen lines here and nothing about it is re-proved.

  ## Step counts

  Read off the dispatch ladder (index `k` sits at `base + 4 * k`):

  * **long string**: idx 0, 1, 2(taken), 5, 6(taken), 10, 11(**not** taken), 12, 13,
    14(`JAL` → idx22) = 10, then idx22–24 = 3, the loop = `7n + 1`, idx32, 33 = 2, and
    the `JALR` = 1. Total **`7 * lenOfLen + 17`**.
  * **long list**: idx 0, 1, 2(taken), 5, 6(taken), 10, 11(taken), 15, 16(taken), 20,
    21 = 11 — one more than the string arm, and it *falls* into idx22 instead of
    jumping — then the same `3 + (7n + 1) + 2 + 1`. Total **`7 * lenOfLen + 18`**.

  The step bound is self-checking: the goal's literal is unified against the sum the
  compositions produce, so a wrong count would not elaborate.

  ## ⭐ Tie to the pure model

  The returned `a0` is pinned as

      BitVec.ofNat 64 (1 + lenOfLen + Nat.fromBytesBE (lenBytes))

  with `lenOfLen` spelled as the model's own `rlpPrefixLongBytesLenOfLen` /
  `rlpPrefixLongListLenOfLen` and `lenBytes = (bs.drop 1).take lenOfLen` — i.e.
  literally the right-hand side of `EL.RLP.decode_span_longBytes` /
  `decode_span_longList` once `readLength`'s value is expanded by
  `readLength_takeBytes`. That expansion needs a successful `readLength`, which is a
  *decode* fact and not something the machine triple can produce on its own, so the
  arithmetic form is the primary statement and the full identification with
  `(EL.RLP.encode item).length` is a separate corollary
  (`..._encode_length_spec_within`) under the stated `decode`/`readLength`
  hypotheses. No statement is weakened to make either close.

  ## Scope

  Proof only. `SpanForm` is **not** widened and nothing is re-graded here — that has
  50+ consumers and is separate follow-up work.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; default elaboration budget.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.ItemSizeLenLoop
import EvmAsm.Evm64.CallingConvention
import EvmAsm.EL.RLP.Properties
import EvmAsm.EL.RLP.LongSpan
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpSpliceHelperArithmetic
namespace EvmAsm.Codegen

namespace RlpItemSizeLongSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Rv64.RLP (risLenLoop rlp_item_size_prog)
open EvmAsm.Codegen.RlpSpliceHelperSpec (ult_zx_of_lt not_ult_zx_of_ge)

/-- Code-membership for a `∀ base` `ofProg` slice: instruction `k` of the program,
    addressed as a concrete `base + OFF` term. Mirrors the file-local macro of the same
    name in `RlpSpliceHelperSpec.lean` (each is `local`, so not importable). -/
local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr _ _ $k _ (by decide) (by decide) (by bv_omega)))

/-! ## Arithmetic helpers

    Two facts, both about the shared long tail: the `SUB` that turns the prefix byte
    into the length-of-length, and the `ADDI`/`ADD` pair that turns
    `x7`/`x28` into the returned span. -/

/-- **`SUB x7, x5, x6`** at idx13/idx21: the zero-extended prefix byte minus a small
    literal is the corresponding `Nat` difference. `c` is `0xB7` (long string) or
    `0xF7` (long list). -/
private theorem ris_zx_sub_lit (b : BitVec 8) (c : Word) (hc : c.toNat < 256)
    (h : c.toNat ≤ b.toNat) :
    (b.zeroExtend 64) - c = BitVec.ofNat 64 (b.toNat - c.toNat) := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- **`ADDI x10, x7, 1` then `ADD x10, x10, x28`** at idx32/idx33: the returned span is
    `1 + lenOfLen + <accumulated length>`, with no wraparound bookkeeping left over
    (`BitVec.ofNat` absorbs it). -/
private theorem ris_long_result (a v : Nat) :
    (BitVec.ofNat 64 a + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 v
      = BitVec.ofNat 64 (1 + a + v) := by
  have h1 : (signExtend12 (1 : BitVec 12) : Word).toNat = 1 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
  omega

/-- The loop's accumulator starts at `Nat.fromBytesBE []`, which is the `LI x28, 0`
    idx22 writes. -/
private theorem ris_acc_init :
    BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) := by
  rw [Nat.fromBytesBE_nil]; decide

/-! ## ⭐ Long-string form (`0xB8 ≤ prefix < 0xC0`) -/

/-- **`rlp_item_size`, long-string form** (`0xB8 ≤ bs[0] ≤ 0xBF`), with the scratch
    registers pinned.

    `a0` returns `1 + lenOfLen + fromBytesBE (the lenOfLen length bytes)`, where
    `lenOfLen = bs[0] - 0xB7` is spelled as the model's own
    `rlpPrefixLongBytesLenOfLen` — the right-hand side of
    `EL.RLP.decode_span_longBytes`; `rlp_item_size_long_string_encode_length_spec_within`
    below completes the identification with `(EL.RLP.encode item).length`.

    Clobbers `t0`–`t2` (`x5`–`x7`) and `t3`–`t6` (`x28`–`x31`); `ra`, `a0` and the
    source region are as stated. Takes `7 * lenOfLen + 17` steps — the `+ 17` is the
    ten-instruction dispatch path, the three-instruction loop setup, the two-instruction
    epilogue, the loop's own exit test and the `JALR`. -/
theorem rlp_item_size_long_string_pinned_spec_within
    (base ptr raVal v5 v6 v7 v28 v29 v30 v31 : Word)
    (bs : List (BitVec 8))
    (h_align : ptr.toNat % 8 = 0)
    (h_lo : 0xb8 ≤ (bs.getD 0 0).toNat)
    (h_hi : (bs.getD 0 0).toNat < 0xc0)
    (h_len : 1 + rlpPrefixLongBytesLenOfLen (bs.getD 0 0) ≤ bs.length)
    (h_nover : ptr.toNat + bs.length ≤ 2 ^ 64)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * rlpPrefixLongBytesLenOfLen (bs.getD 0 0) + 17) base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64
         (1 + rlpPrefixLongBytesLenOfLen (bs.getD 0 0)
            + Nat.fromBytesBE ((bs.drop 1).take (rlpPrefixLongBytesLenOfLen (bs.getD 0 0))))) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  obtain ⟨n, hn⟩ : ∃ n, rlpPrefixLongBytesLenOfLen (bs.getD 0 0) = n := ⟨_, rfl⟩
  have hn' : (bs.getD 0 0).toNat - 183 = n := hn
  rw [hn] at h_len ⊢
  have h_len0 : 0 < bs.length := by omega
  have hn_hi : n ≤ 8 := by omega
  rw [rlpItemSize_prog_eq_verified_prog]
  set CR := CodeReq.ofProg base rlp_item_size_prog with hCR
  have h0 : (bs[0]'h_len0) = bs.getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_len0]; rfl
  -- ══ idx0 (base+0): LBU x5, 0(x10) — the prefix byte ══
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 ptr v5 base bs 0 (by decide) h_align h_len0
      (by have := ptr.isLt; omega) (h_valid 0 h_len0))
    (by rw [hCR]; cmem 0)
  rw [show ptr + BitVec.ofNat 64 0 = ptr from by bv_omega, h0] at hlbu
  -- ══ idx1 (base+4): LI x6, 0x80 ══
  have hli1 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli1
  -- ══ idx2 (base+8): BGEU x5, x6, +12 — TAKEN (b ≥ 0xb8 ≥ 0x80) → base+20 ══
  have hbr2 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr2
  have ht2 := cpsBranchWithin_takenStripPure2 hbr2 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0x80 : Word)
        (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- ══ idx5 (base+20): LI x6, 0xb8 ══
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 20) (by decide))
    (by rw [hCR]; cmem 5)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hli5
  -- ══ idx6 (base+24): BGEU x5, x6, +16 — TAKEN (b ≥ 0xb8) → base+40 ══
  have hbr6 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 6)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xb8 : Word) (base + 24))
  rw [show (base + 24 : Word) + signExtend13 (16 : BitVec 13) = base + 40 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbr6
  have ht6 := cpsBranchWithin_takenStripPure2 hbr6 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xb8 : Word)
        (by rw [show ((0xb8 : Word)).toNat = 184 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- ══ idx10 (base+40): LI x6, 0xc0 ══
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 40) (by decide))
    (by rw [hCR]; cmem 10)
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hli10
  -- ══ idx11 (base+44): BGEU x5, x6, +16 — NOT taken (b < 0xc0) → base+48 ══
  have hbr11 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 11)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xc0 : Word) (base + 44))
  rw [show (base + 44 : Word) + signExtend13 (16 : BitVec 13) = base + 60 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hbr11
  have hnt11 := cpsBranchWithin_ntakenStripPure2 hbr11 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2
      (ult_zx_of_lt _ _ (by rw [show ((0xc0 : Word)).toNat = 192 from by decide]; exact h_hi)))
  -- ══ idx12 (base+48): LI x6, 0xb7 ══
  have hli12 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xc0 : Word) (0xb7 : Word) (base + 48) (by decide))
    (by rw [hCR]; cmem 12)
  rw [show (base + 48 : Word) + 4 = base + 52 from by bv_omega] at hli12
  -- ══ idx13 (base+52): SUB x7, x5, x6 — x7 := lenOfLen ══
  have hsub13 := liftCode (cr' := CR)
    (sub_spec_gen_within .x7 .x5 .x6 ((bs.getD 0 0).zeroExtend 64) (0xb7 : Word) v7
      (base + 52) (by decide))
    (by rw [hCR]; cmem 13)
  rw [show (base + 52 : Word) + 4 = base + 56 from by bv_omega,
      ris_zx_sub_lit (bs.getD 0 0) (0xb7 : Word) (by decide)
        (by rw [show ((0xb7 : Word)).toNat = 183 from by decide]; omega),
      show ((0xb7 : Word)).toNat = 183 from by decide, hn'] at hsub13
  -- ══ idx14 (base+56): JAL x0, +32 → base+88 (shared long tail) ══
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (32 : BitVec 21) (base + 56))
    (by rw [hCR]; cmem 14)
  rw [show (base + 56 : Word) + signExtend21 (32 : BitVec 21) = base + 88 from by
        rw [show signExtend21 (32 : BitVec 21) = (32 : Word) from by decide]; bv_omega] at hjal
  -- ══ idx22 (base+88): LI x28, 0 — accumulator ══
  have hli22 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 v28 (0 : Word) (base + 88) (by decide))
    (by rw [hCR]; cmem 22)
  rw [show (base + 88 : Word) + 4 = base + 92 from by bv_omega] at hli22
  -- ══ idx23 (base+92): ADDI x29, x10, 1 — cursor := ptr + 1 ══
  have ha23 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x10 v29 ptr (1 : BitVec 12) (base + 92) (by decide))
    (by rw [hCR]; cmem 23)
  rw [show (base + 92 : Word) + 4 = base + 96 from by bv_omega,
      show ptr + signExtend12 (1 : BitVec 12) = ptr + BitVec.ofNat 64 1 from by
        rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]] at ha23
  -- ══ idx24 (base+96): MV x30, x7 — counter := lenOfLen ══
  have hmv24 := liftCode (cr' := CR)
    (mv_spec_gen_within .x30 .x7 (BitVec.ofNat 64 n) v30 (base + 96) (by decide))
    (by rw [hCR]; cmem 24)
  rw [show (base + 96 : Word) + 4 = base + 100 from by bv_omega] at hmv24
  -- ══ ⭐ idx25–31 (base+100 → base+128): the length loop, cited whole ══
  have hloop : cpsTripleWithin (7 * n + 1) (base + 100) (base + 128) CR
      ((.x30 ↦ᵣ BitVec.ofNat 64 n) ** (.x29 ↦ᵣ (ptr + BitVec.ofNat 64 1)) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8)))) **
       (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      ((.x30 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) **
       (.x28 ↦ᵣ BitVec.ofNat 64
         (Nat.fromBytesBE (([] : List (BitVec 8)) ++ (bs.drop 1).take n))) **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) :=
    risLenLoop base ptr v31 bs [] 1 n h_align (by omega) (by omega)
      (by simpa using hn_hi)
      (fun k hk => h_valid (1 + k) (by omega))
  rw [ris_acc_init, List.nil_append] at hloop
  -- ══ idx32 (base+128): ADDI x10, x7, 1 ══
  have ha32 := liftCode (cr' := CR)
    (addi_spec_gen_within .x10 .x7 ptr (BitVec.ofNat 64 n) (1 : BitVec 12) (base + 128)
      (by decide))
    (by rw [hCR]; cmem 32)
  rw [show (base + 128 : Word) + 4 = base + 132 from by bv_omega] at ha32
  -- ══ idx33 (base+132): ADD x10, x10, x28 ══
  have ha33 := liftCode (cr' := CR)
    (add_spec_gen_rd_eq_rs1_within .x10 .x28
      (BitVec.ofNat 64 n + signExtend12 (1 : BitVec 12))
      (BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) (base + 132) (by decide))
    (by rw [hCR]; cmem 33)
  rw [show (base + 132 : Word) + 4 = base + 136 from by bv_omega,
      ris_long_result n (Nat.fromBytesBE ((bs.drop 1).take n))] at ha33
  -- ══ idx34 (base+136): ret ══
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 136) raVal)
    (by rw [hCR]; cmem 34)
  -- ══ frames ══
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hli1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli1
  have ht2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ht2
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli5
  have ht6F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ht6
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli10
  have hnt11F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hnt11
  have hli12F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli12
  have hsub13F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hsub13
  have hjalF : cpsTripleWithin 1 (base + 56) (base + 88) CR
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
       ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
       ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) :=
    cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
         ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
         ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
        (by pcf) hjal)
  have hli22F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli22
  have ha23F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x28 : Reg) ↦ᵣ (0 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha23
  have hmv24F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
     ((.x28 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 1)) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hmv24
  have hloopF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n))
    (by pcf) hloop
  have ha32F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) **
     ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) ** ((.x30 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha32
  have ha33F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) ** ((.x30 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha33
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (1 + n + Nat.fromBytesBE ((bs.drop 1).take n))) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) **
     ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) ** ((.x30 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hret
  -- ══ compose: 10 dispatch + 3 setup + (7n+1) loop + 2 epilogue + 1 ret = 7n+17 ══
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hli1F
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 ht2F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli5F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 ht6F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 hli10F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 hnt11F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hli12F
  have hc8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc7 hsub13F
  have hc9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc8 hjalF
  have hc10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc9 hli22F
  have hc11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc10 ha23F
  have hc12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc11 hmv24F
  have hc13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc12 hloopF
  have hc14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc13 ha32F
  have hc15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc14 ha33F
  have hc16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc15 hretF
  rw [show 7 * n + 17
      = 1+1+1+1+1+1+1+1+1+1+1+1+1 + (7 * n + 1) + 1 + 1 + 1 from by omega]
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc16
  have hq1 : (((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0xb7 : Word)) **
       (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) **
         (((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) **
          (((.x30 : Reg) ↦ᵣ (0 : Word)) **
           (((.x1 : Reg) ↦ᵣ raVal) **
            ((.x10 : Reg) ↦ᵣ
              BitVec.ofNat 64 (1 + n + Nat.fromBytesBE ((bs.drop 1).take n))) **
            regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs))))))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _)
      (sepConj_mono (regIs_to_regOwn .x7 _)
        (sepConj_mono (regIs_to_regOwn .x28 _)
          (sepConj_mono (regIs_to_regOwn .x29 _)
            (sepConj_mono (regIs_to_regOwn .x30 _) (fun _ hh => hh)))))) h hq1
  xperm_hyp hq2

/-! ## ⭐ Long-list form (`0xF8 ≤ prefix`) -/

/-- **`rlp_item_size`, long-list form** (`0xF8 ≤ bs[0]`), with the scratch registers
    pinned.

    Identical to the long-string arm from idx22 on — both fall into the same tail — and
    differs only in the dispatch: the ladder runs one branch further (idx11 *taken* to
    idx15, idx16 taken to idx20) and the subtrahend is `0xF7` rather than `0xB7`. Since
    idx21 falls straight into idx22 instead of jumping like idx14 does, this arm spends
    eleven dispatch steps to the string arm's ten, hence `7 * lenOfLen + 18`.

    `lenOfLen` is spelled as the model's own `rlpPrefixLongListLenOfLen` — the
    right-hand side of `EL.RLP.decode_span_longList`;
    `rlp_item_size_long_list_encode_length_spec_within` below completes the
    identification with `(EL.RLP.encode item).length`. -/
theorem rlp_item_size_long_list_pinned_spec_within
    (base ptr raVal v5 v6 v7 v28 v29 v30 v31 : Word)
    (bs : List (BitVec 8))
    (h_align : ptr.toNat % 8 = 0)
    (h_lo : 0xf8 ≤ (bs.getD 0 0).toNat)
    (h_len : 1 + rlpPrefixLongListLenOfLen (bs.getD 0 0) ≤ bs.length)
    (h_nover : ptr.toNat + bs.length ≤ 2 ^ 64)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * rlpPrefixLongListLenOfLen (bs.getD 0 0) + 18) base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64
         (1 + rlpPrefixLongListLenOfLen (bs.getD 0 0)
            + Nat.fromBytesBE ((bs.drop 1).take (rlpPrefixLongListLenOfLen (bs.getD 0 0))))) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  obtain ⟨n, hn⟩ : ∃ n, rlpPrefixLongListLenOfLen (bs.getD 0 0) = n := ⟨_, rfl⟩
  have hn' : (bs.getD 0 0).toNat - 247 = n := hn
  have h_hi : (bs.getD 0 0).toNat < 256 := (bs.getD 0 0).isLt
  rw [hn] at h_len ⊢
  have h_len0 : 0 < bs.length := by omega
  have hn_hi : n ≤ 8 := by omega
  rw [rlpItemSize_prog_eq_verified_prog]
  set CR := CodeReq.ofProg base rlp_item_size_prog with hCR
  have h0 : (bs[0]'h_len0) = bs.getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_len0]; rfl
  -- ══ idx0 (base+0): LBU x5, 0(x10) — the prefix byte ══
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 ptr v5 base bs 0 (by decide) h_align h_len0
      (by have := ptr.isLt; omega) (h_valid 0 h_len0))
    (by rw [hCR]; cmem 0)
  rw [show ptr + BitVec.ofNat 64 0 = ptr from by bv_omega, h0] at hlbu
  -- ══ idx1 (base+4): LI x6, 0x80 ══
  have hli1 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli1
  -- ══ idx2 (base+8): BGEU x5, x6, +12 — TAKEN (b ≥ 0xf8 ≥ 0x80) → base+20 ══
  have hbr2 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr2
  have ht2 := cpsBranchWithin_takenStripPure2 hbr2 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0x80 : Word)
        (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- ══ idx5 (base+20): LI x6, 0xb8 ══
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 20) (by decide))
    (by rw [hCR]; cmem 5)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hli5
  -- ══ idx6 (base+24): BGEU x5, x6, +16 — TAKEN (b ≥ 0xf8 ≥ 0xb8) → base+40 ══
  have hbr6 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 6)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xb8 : Word) (base + 24))
  rw [show (base + 24 : Word) + signExtend13 (16 : BitVec 13) = base + 40 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbr6
  have ht6 := cpsBranchWithin_takenStripPure2 hbr6 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xb8 : Word)
        (by rw [show ((0xb8 : Word)).toNat = 184 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- ══ idx10 (base+40): LI x6, 0xc0 ══
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 40) (by decide))
    (by rw [hCR]; cmem 10)
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hli10
  -- ══ idx11 (base+44): BGEU x5, x6, +16 — TAKEN (b ≥ 0xf8 ≥ 0xc0) → base+60 ══
  have hbr11 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 11)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xc0 : Word) (base + 44))
  rw [show (base + 44 : Word) + signExtend13 (16 : BitVec 13) = base + 60 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hbr11
  have ht11 := cpsBranchWithin_takenStripPure2 hbr11 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xc0 : Word)
        (by rw [show ((0xc0 : Word)).toNat = 192 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- ══ idx15 (base+60): LI x6, 0xf8 ══
  have hli15 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 60) (by decide))
    (by rw [hCR]; cmem 15)
  rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at hli15
  -- ══ idx16 (base+64): BGEU x5, x6, +16 — TAKEN (b ≥ 0xf8) → base+80 ══
  have hbr16 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 16)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xf8 : Word) (base + 64))
  rw [show (base + 64 : Word) + signExtend13 (16 : BitVec 13) = base + 80 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 64 : Word) + 4 = base + 68 from by bv_omega] at hbr16
  have ht16 := cpsBranchWithin_takenStripPure2 hbr16 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xf8 : Word)
        (by rw [show ((0xf8 : Word)).toNat = 248 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- ══ idx20 (base+80): LI x6, 0xf7 ══
  have hli20 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 80) (by decide))
    (by rw [hCR]; cmem 20)
  rw [show (base + 80 : Word) + 4 = base + 84 from by bv_omega] at hli20
  -- ══ idx21 (base+84): SUB x7, x5, x6 — x7 := lenOfLen; falls into the shared tail ══
  have hsub21 := liftCode (cr' := CR)
    (sub_spec_gen_within .x7 .x5 .x6 ((bs.getD 0 0).zeroExtend 64) (0xf7 : Word) v7
      (base + 84) (by decide))
    (by rw [hCR]; cmem 21)
  rw [show (base + 84 : Word) + 4 = base + 88 from by bv_omega,
      ris_zx_sub_lit (bs.getD 0 0) (0xf7 : Word) (by decide)
        (by rw [show ((0xf7 : Word)).toNat = 247 from by decide]; omega),
      show ((0xf7 : Word)).toNat = 247 from by decide, hn'] at hsub21
  -- ══ idx22 (base+88): LI x28, 0 — accumulator ══
  have hli22 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 v28 (0 : Word) (base + 88) (by decide))
    (by rw [hCR]; cmem 22)
  rw [show (base + 88 : Word) + 4 = base + 92 from by bv_omega] at hli22
  -- ══ idx23 (base+92): ADDI x29, x10, 1 — cursor := ptr + 1 ══
  have ha23 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x10 v29 ptr (1 : BitVec 12) (base + 92) (by decide))
    (by rw [hCR]; cmem 23)
  rw [show (base + 92 : Word) + 4 = base + 96 from by bv_omega,
      show ptr + signExtend12 (1 : BitVec 12) = ptr + BitVec.ofNat 64 1 from by
        rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]] at ha23
  -- ══ idx24 (base+96): MV x30, x7 — counter := lenOfLen ══
  have hmv24 := liftCode (cr' := CR)
    (mv_spec_gen_within .x30 .x7 (BitVec.ofNat 64 n) v30 (base + 96) (by decide))
    (by rw [hCR]; cmem 24)
  rw [show (base + 96 : Word) + 4 = base + 100 from by bv_omega] at hmv24
  -- ══ ⭐ idx25–31 (base+100 → base+128): the length loop, cited whole ══
  have hloop : cpsTripleWithin (7 * n + 1) (base + 100) (base + 128) CR
      ((.x30 ↦ᵣ BitVec.ofNat 64 n) ** (.x29 ↦ᵣ (ptr + BitVec.ofNat 64 1)) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8)))) **
       (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      ((.x30 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) **
       (.x28 ↦ᵣ BitVec.ofNat 64
         (Nat.fromBytesBE (([] : List (BitVec 8)) ++ (bs.drop 1).take n))) **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) :=
    risLenLoop base ptr v31 bs [] 1 n h_align (by omega) (by omega)
      (by simpa using hn_hi)
      (fun k hk => h_valid (1 + k) (by omega))
  rw [ris_acc_init, List.nil_append] at hloop
  -- ══ idx32 (base+128): ADDI x10, x7, 1 ══
  have ha32 := liftCode (cr' := CR)
    (addi_spec_gen_within .x10 .x7 ptr (BitVec.ofNat 64 n) (1 : BitVec 12) (base + 128)
      (by decide))
    (by rw [hCR]; cmem 32)
  rw [show (base + 128 : Word) + 4 = base + 132 from by bv_omega] at ha32
  -- ══ idx33 (base+132): ADD x10, x10, x28 ══
  have ha33 := liftCode (cr' := CR)
    (add_spec_gen_rd_eq_rs1_within .x10 .x28
      (BitVec.ofNat 64 n + signExtend12 (1 : BitVec 12))
      (BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) (base + 132) (by decide))
    (by rw [hCR]; cmem 33)
  rw [show (base + 132 : Word) + 4 = base + 136 from by bv_omega,
      ris_long_result n (Nat.fromBytesBE ((bs.drop 1).take n))] at ha33
  -- ══ idx34 (base+136): ret ══
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 136) raVal)
    (by rw [hCR]; cmem 34)
  -- ══ frames ══
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hli1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli1
  have ht2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ht2
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli5
  have ht6F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ht6
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli10
  have ht11F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ht11
  have hli15F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli15
  have ht16F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ht16
  have hli20F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli20
  have hsub21F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hsub21
  have hli22F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli22
  have ha23F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x28 : Reg) ↦ᵣ (0 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha23
  have hmv24F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
     ((.x28 : Reg) ↦ᵣ (0 : Word)) ** ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 1)) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hmv24
  have hloopF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n))
    (by pcf) hloop
  have ha32F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) **
     ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) ** ((.x30 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha32
  have ha33F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) ** ((.x30 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha33
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (1 + n + Nat.fromBytesBE ((bs.drop 1).take n))) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
     ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
     ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) **
     ((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) ** ((.x30 : Reg) ↦ᵣ (0 : Word)) **
     regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hret
  -- ══ compose: 11 dispatch + 3 setup + (7n+1) loop + 2 epilogue + 1 ret = 7n+18 ══
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hli1F
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 ht2F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli5F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 ht6F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 hli10F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 ht11F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hli15F
  have hc8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc7 ht16F
  have hc9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc8 hli20F
  have hc10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc9 hsub21F
  have hc11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc10 hli22F
  have hc12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc11 ha23F
  have hc13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc12 hmv24F
  have hc14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc13 hloopF
  have hc15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc14 ha32F
  have hc16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc15 ha33F
  have hc17 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc16 hretF
  rw [show 7 * n + 18
      = 1+1+1+1+1+1+1+1+1+1+1+1+1+1 + (7 * n + 1) + 1 + 1 + 1 from by omega]
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc17
  have hq1 : (((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0xf7 : Word)) **
       (((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop 1).take n))) **
         (((.x29 : Reg) ↦ᵣ (ptr + BitVec.ofNat 64 (1 + n))) **
          (((.x30 : Reg) ↦ᵣ (0 : Word)) **
           (((.x1 : Reg) ↦ᵣ raVal) **
            ((.x10 : Reg) ↦ᵣ
              BitVec.ofNat 64 (1 + n + Nat.fromBytesBE ((bs.drop 1).take n))) **
            regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs))))))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _)
      (sepConj_mono (regIs_to_regOwn .x7 _)
        (sepConj_mono (regIs_to_regOwn .x28 _)
          (sepConj_mono (regIs_to_regOwn .x29 _)
            (sepConj_mono (regIs_to_regOwn .x30 _) (fun _ hh => hh)))))) h hq1
  xperm_hyp hq2

/-! ## ⭐ Tie to the pure model: `a0 = (encode item).length`

    The two triples above return `1 + lenOfLen + fromBytesBE lenBytes`, which is the
    right-hand side of `decode_span_longBytes`/`decode_span_longList` with
    `readLength`'s value expanded by `readLength_takeBytes`. Expanding it needs a
    successful `decode` and a successful `readLength` — decoder facts a machine triple
    cannot manufacture — so the identification is a corollary under exactly those two
    hypotheses. The buffer-length bound `1 + lenOfLen ≤ bs.length` is *derived* here
    rather than assumed, since `readLength` consuming `lenOfLen` bytes already implies
    it (`readLength_length`). -/

/-- **Long-string form, tied to the model.** On a buffer whose head decodes as a long
    string, `a0` is exactly `(EL.RLP.encode item).length` — the item's full encoded
    byte span, the same quantity the short-form dispatch
    `RlpSpliceHelperSpec.rlp_item_size_form_own_spec_within` returns. -/
theorem rlp_item_size_long_string_encode_length_spec_within
    (base ptr raVal v5 v6 v7 v28 v29 v30 v31 : Word)
    (bs : List (BitVec 8)) (item : RLPItem) (rest lenRest : List Byte) (lenVal : Nat)
    (h_align : ptr.toNat % 8 = 0)
    (h_lo : 0xb8 ≤ (bs.getD 0 0).toNat)
    (h_hi : (bs.getD 0 0).toNat < 0xc0)
    (h_nover : ptr.toNat + bs.length ≤ 2 ^ 64)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_decode : decode bs = some (item, rest))
    (h_read : readLength (bs.drop 1) (rlpPrefixLongBytesLenOfLen (bs.getD 0 0))
      = some (lenVal, lenRest)) :
    cpsTripleWithin (7 * rlpPrefixLongBytesLenOfLen (bs.getD 0 0) + 17) base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode item).length) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  have hkey : 1 + rlpPrefixLongBytesLenOfLen (bs.getD 0 0) ≤ bs.length
      ∧ (encode item).length
          = 1 + rlpPrefixLongBytesLenOfLen (bs.getD 0 0)
              + Nat.fromBytesBE
                  ((bs.drop 1).take (rlpPrefixLongBytesLenOfLen (bs.getD 0 0))) := by
    cases bs with
    | nil =>
      rw [decode_eq_decodeAux_length, decodeAux_nil] at h_decode
      exact absurd h_decode (by simp)
    | cons pfx rest0 =>
      rw [show (pfx :: rest0).getD 0 0 = pfx from rfl] at h_lo h_hi
      obtain ⟨lenBytes, htk, -, hval⟩ := readLength_takeBytes h_read
      have htk' : takeBytes rest0 (rlpPrefixLongBytesLenOfLen pfx) = some (lenBytes, lenRest) :=
        htk
      unfold takeBytes at htk'
      by_cases hge : rest0.length ≥ rlpPrefixLongBytesLenOfLen pfx
      · rw [if_pos hge] at htk'
        simp only [Option.some.injEq, Prod.mk.injEq] at htk'
        refine ⟨show 1 + rlpPrefixLongBytesLenOfLen pfx ≤ rest0.length + 1 from by omega, ?_⟩
        show (encode item).length
          = 1 + rlpPrefixLongBytesLenOfLen pfx
              + Nat.fromBytesBE (rest0.take (rlpPrefixLongBytesLenOfLen pfx))
        rw [decode_span_longBytes h_decode h_lo (by omega) h_read, hval, htk'.1]
      · rw [if_neg hge] at htk'
        exact absurd htk' (by simp)
  rw [hkey.2]
  exact rlp_item_size_long_string_pinned_spec_within base ptr raVal v5 v6 v7 v28 v29 v30 v31
    bs h_align h_lo h_hi hkey.1 h_nover h_valid

/-- **Long-list form, tied to the model.** Same statement as the long-string corollary,
    over `decode_span_longList`. -/
theorem rlp_item_size_long_list_encode_length_spec_within
    (base ptr raVal v5 v6 v7 v28 v29 v30 v31 : Word)
    (bs : List (BitVec 8)) (item : RLPItem) (rest lenRest : List Byte) (lenVal : Nat)
    (h_align : ptr.toNat % 8 = 0)
    (h_lo : 0xf8 ≤ (bs.getD 0 0).toNat)
    (h_nover : ptr.toNat + bs.length ≤ 2 ^ 64)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_decode : decode bs = some (item, rest))
    (h_read : readLength (bs.drop 1) (rlpPrefixLongListLenOfLen (bs.getD 0 0))
      = some (lenVal, lenRest)) :
    cpsTripleWithin (7 * rlpPrefixLongListLenOfLen (bs.getD 0 0) + 18) base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode item).length) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  have hkey : 1 + rlpPrefixLongListLenOfLen (bs.getD 0 0) ≤ bs.length
      ∧ (encode item).length
          = 1 + rlpPrefixLongListLenOfLen (bs.getD 0 0)
              + Nat.fromBytesBE
                  ((bs.drop 1).take (rlpPrefixLongListLenOfLen (bs.getD 0 0))) := by
    cases bs with
    | nil =>
      rw [decode_eq_decodeAux_length, decodeAux_nil] at h_decode
      exact absurd h_decode (by simp)
    | cons pfx rest0 =>
      obtain ⟨lenBytes, htk, -, hval⟩ := readLength_takeBytes h_read
      have htk' : takeBytes rest0 (rlpPrefixLongListLenOfLen pfx) = some (lenBytes, lenRest) :=
        htk
      unfold takeBytes at htk'
      by_cases hge : rest0.length ≥ rlpPrefixLongListLenOfLen pfx
      · rw [if_pos hge] at htk'
        simp only [Option.some.injEq, Prod.mk.injEq] at htk'
        refine ⟨show 1 + rlpPrefixLongListLenOfLen pfx ≤ rest0.length + 1 from by omega, ?_⟩
        show (encode item).length
          = 1 + rlpPrefixLongListLenOfLen pfx
              + Nat.fromBytesBE (rest0.take (rlpPrefixLongListLenOfLen pfx))
        rw [decode_span_longList h_decode h_lo h_read, hval, htk'.1]
      · rw [if_neg hge] at htk'
        exact absurd htk' (by simp)
  rw [hkey.2]
  exact rlp_item_size_long_list_pinned_spec_within base ptr raVal v5 v6 v7 v28 v29 v30 v31
    bs h_align h_lo hkey.1 h_nover h_valid

/-! ## ⭐ Reachability of the two gates (#12014's ruling)

    @pirapira ruled on #12014 that a `.conditional` row needs a **reachable** witness, not
    merely a consistent one. Both arms' gates are input-domain conditions on the prefix
    byte, so a witness is an actual RLP item the guest can be handed.

    ⚠️ Scope of these witnesses, stated so the registry claim is not read wider than it is:
    they exhibit the **input-domain** gate (`h_lo`/`h_hi`/`h_len`). The remaining
    preconditions — `h_align`, `h_nover`, `h_valid` — are ABI/resource obligations on the
    caller's buffer, not domain restrictions on RLP, and are discharged wherever the
    routine is actually called rather than being properties of an input. -/

/-- A canonical 56-byte long string: prefix `0xb8` (one length byte), length `0x38 = 56`,
    then 56 content bytes. 56 is exactly the short/long boundary, so this is the *smallest*
    input the long-string arm applies to — the arm is not reachable only in the large. -/
private def longStringSample : List (BitVec 8) :=
  (0xb8 : BitVec 8) :: (0x38 : BitVec 8) :: List.replicate 56 (0x41 : BitVec 8)

/-- The long-string arm's input-domain gate is satisfied, and the sample is a complete
    item: its total encoded length `1 + 1 + 56 = 58` is its own length. -/
theorem longStringSample_reachable :
    0xb8 ≤ (longStringSample.getD 0 0).toNat
      ∧ (longStringSample.getD 0 0).toNat < 0xc0
      ∧ 1 + rlpPrefixLongBytesLenOfLen (longStringSample.getD 0 0) ≤ longStringSample.length
      ∧ 1 + rlpPrefixLongBytesLenOfLen (longStringSample.getD 0 0)
          + Nat.fromBytesBE ((longStringSample.drop 1).take
              (rlpPrefixLongBytesLenOfLen (longStringSample.getD 0 0)))
        = longStringSample.length := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- A 56-byte long list: prefix `0xf8`, length `0x38 = 56`, payload 56 bytes. Same
    boundary argument. The payload's own well-formedness is not part of this arm's gate —
    `rlp_item_size` computes a span and does not descend. -/
private def longListSample : List (BitVec 8) :=
  (0xf8 : BitVec 8) :: (0x38 : BitVec 8) :: List.replicate 56 (0x41 : BitVec 8)

/-- The long-list arm's input-domain gate is satisfied, with the same span identity. -/
theorem longListSample_reachable :
    0xf8 ≤ (longListSample.getD 0 0).toNat
      ∧ 1 + rlpPrefixLongListLenOfLen (longListSample.getD 0 0) ≤ longListSample.length
      ∧ 1 + rlpPrefixLongListLenOfLen (longListSample.getD 0 0)
          + Nat.fromBytesBE ((longListSample.drop 1).take
              (rlpPrefixLongListLenOfLen (longListSample.getD 0 0)))
        = longListSample.length := by
  refine ⟨by decide, by decide, by decide⟩

end RlpItemSizeLongSpec

end EvmAsm.Codegen
