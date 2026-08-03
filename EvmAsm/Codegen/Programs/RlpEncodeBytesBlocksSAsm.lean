/-
  EvmAsm.Codegen.Programs.RlpEncodeBytesBlocksSAsm

  **The machine blocks of `rlp_encode_bytes`** (#10780 item 2, stage 2): the
  three loops and, below them, the straight-line and branch blocks.  The pure
  model layer lives in `RlpEncodeBytesSAsm.lean`, the `bc` ladder in
  `RlpEncodeBytesLadderSAsm.lean`; splitting one routine across sibling modules
  follows `WithdrawalDecodeClose` → `Close2..5` (hard 1500-line cap).

  ## The three loops, and why they are three proofs

  The two payload copy loops ([19]-[25] and [63]-[70]) are the same six
  instructions, and the length-of-length loop ([56]-[62]) shares their shape.
  They cannot share a lemma: `rebBase` is the concrete numeral
  `GuestAddrs.rlp_encode_bytes`, so `runBlock` discharges code membership by
  evaluation at concrete addresses — a lemma generic over the loop-head address
  leaves membership unprovable.  Same reason `reubCopyLoop` and
  `cu256_loop_spec_within` coexist.

  ⭐ The two copy loops' scratch registers differ **and it is load-bearing**:
  the short loop scratches `x28`, the long loop scratches `x30` because `x28`
  still holds `bc`, which [71] needs for the written length `bc + 1 + len`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpEncodeBytesLadderSAsm
import EvmAsm.Rv64.SAsm.MultiDword

namespace EvmAsm.Codegen

namespace RlpEncodeBytesSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
-- `getByteAt` is `EvmAsm.Rv64`'s, already open above.
open EvmAsm.Rv64.RLP (copyN copyN_zero copyN_succ copyN_length
  word_ofNat_succ_dec word_ofNat_succ_ne_zero)

/-- Code-membership for instruction `k` (local copy — local macros do not
    export across modules). -/
local macro "rebmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr rebBase rlpEncodeBytes_prog $k _
        (by rw [reb_prog_length]; norm_num)
        (by rw [reb_prog_length]; norm_num) (by rfl)))

/-! ## §1  Hoisted arithmetic

    The `reub_jal_back` lesson: a `bv_omega` on a concrete linked address inside
    an induction's `succ` branch blows `maxRecDepth`, so every such fact is a
    top-level lemma. -/

/-- `[25] JAL x0, -24` returns to the short copy loop head. -/
private theorem short_jal_back :
    (rebBase + 100) + signExtend21 (-24 : BitVec 21) = rebBase + 76 := by
  rw [show signExtend21 (-24 : BitVec 21) = -(24 : Word) from by decide]
  bv_omega

/-- `[62] JAL x0, -24` returns to the length-of-length loop head. -/
private theorem lol_jal_back :
    (rebBase + 248) + signExtend21 (-24 : BitVec 21) = rebBase + 224 := by
  rw [show signExtend21 (-24 : BitVec 21) = -(24 : Word) from by decide]
  bv_omega

/-- `[70] JAL x0, -24` returns to the long copy loop head. -/
private theorem long_jal_back :
    (rebBase + 280) + signExtend21 (-24 : BitVec 21) = rebBase + 256 := by
  rw [show signExtend21 (-24 : BitVec 21) = -(24 : Word) from by decide]
  bv_omega

/-- `[57] SLLI x30, x29, 3` at a counter below 8 is byte-scaling. -/
private theorem lol_slli (m : Nat) (h : m < 8) :
    BitVec.ofNat 64 m <<< (3 : BitVec 6).toNat = BitVec.ofNat 64 (8 * m) := by
  interval_cases m <;> decide

/-- `[58] SRL`'s low-6-bit shift is exact: `8m ≤ 56 < 64`. -/
private theorem lol_srl_exp (m : Nat) (h : m < 8) :
    (BitVec.ofNat 64 (8 * m)).toNat % 64 = 8 * m := by
  rw [BitVec.toNat_ofNat]
  omega

/-- A decrement in the invariant's `- 1` form.  Unconditional: `mod 2 ^ 64`
    absorbs the reduction. -/
private theorem cnt_dec (v : Word) :
    v + signExtend12 (-1 : BitVec 12) = v - 1 := by
  rw [show signExtend12 (-1 : BitVec 12) = -(1 : Word) from by decide]
  bv_omega

/-- A cursor advance by one byte. -/
private theorem cur_up (base : Word) (i : Nat) :
    (base + BitVec.ofNat 64 i) + signExtend12 (1 : BitVec 12)
      = base + BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

/-- The empty length-of-length counter reads as `-1`, which fires the exit
    `BLT`. -/
private theorem lol_zero_cnt : BitVec.ofNat 64 0 - 1 = (-1 : Word) := by decide

/-! ## §2  The length-of-length loop ([56]-[62])

    Writes the `m` big-endian bytes of `len` — `writeShift` on the region, tied
    to `Nat.toBytesBE` by `beShift_eq_toBytesBE` at `m = bc`.  The counter is
    **signed**: it runs `bc-1` down to `-1`, and the `BLT` at the head fires on
    `-1` (`slt_neg_one`) and falls through on `0..7` (`slt_small_false`). -/

set_option maxRecDepth 8000 in
/-- **One length-of-length iteration** ([57]-[61], `rebBase+228 → rebBase+248`):
    at counter `m`, store big-endian byte `m` of `len` and step the cursors. -/
theorem rebLolBody (outBase v30 v31 len : Word) (dst : List Byte)
    (di m : Nat) (hm : m < 8)
    (halign : outBase.toNat % 8 = 0) (hdi : di < dst.length)
    (hover : outBase.toNat + di < 2 ^ 64)
    (hvalid : isValidByteAccess (outBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 (rebBase + 228) (rebBase + 248) rebCode
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x6 : Reg) ↦ᵣ len) **
       ((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       bytesRegion outBase dst)
      (((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 m - 1)) **
       ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * m)) **
       ((.x31 : Reg) ↦ᵣ (len >>> (8 * m))) ** ((.x6 : Reg) ↦ᵣ len) **
       ((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 (di + 1))) **
       bytesRegion outBase
         (dst.set di (BitVec.ofNat 8 (len.toNat / 256 ^ m % 256)))) := by
  have hslli := slli_spec_gen_within .x30 .x29 v30 (BitVec.ofNat 64 m)
    (3 : BitVec 6) (rebBase + 228) (by decide)
  rw [show rebBase + 228 + 4 = rebBase + 232 from by bv_omega,
      lol_slli m hm] at hslli
  have hsrl := srl_spec_gen_within .x31 .x6 .x30 v31 len (BitVec.ofNat 64 (8 * m))
    (rebBase + 232) (by decide)
  rw [show rebBase + 232 + 4 = rebBase + 236 from by bv_omega,
      lol_srl_exp m hm] at hsrl
  have hsb := bytesRegion_sb_within .x7 .x31 outBase (len >>> (8 * m))
    (rebBase + 236) dst di halign hdi hover hvalid
  rw [show rebBase + 236 + 4 = rebBase + 240 from by bv_omega,
      truncate_shift_eq len m] at hsb
  have ha7 := addi_spec_gen_same_within .x7 (outBase + BitVec.ofNat 64 di)
    (1 : BitVec 12) (rebBase + 240) (by nofun)
  rw [show rebBase + 240 + 4 = rebBase + 244 from by bv_omega,
      cur_up outBase di] at ha7
  have ha29 := addi_spec_gen_same_within .x29 (BitVec.ofNat 64 m)
    (-1 : BitVec 12) (rebBase + 244) (by nofun)
  rw [show rebBase + 244 + 4 = rebBase + 248 from by bv_omega,
      cnt_dec (BitVec.ofNat 64 m)] at ha29
  runBlock hslli hsrl hsb ha7 ha29

set_option maxRecDepth 8000 in
/-- **The length-of-length loop** ([56]-[62], `rebBase+224 → rebBase+252`), by
    induction on the remaining count `m`: writes `writeShift dst di len.toNat m`
    in `7*m + 1` steps.

    The invariant's counter is `ofNat 64 m - 1`: at `m = 0` that is `-1` and the
    signed `BLT` fires; at `m + 1` it is `ofNat m` (`ofNat_succ_sub_one`) and
    the guard falls through (`slt_small_false`, sound because `m ≤ 8` — the
    counter never exceeds `bc - 1 ≤ 7`). -/
theorem rebLolLoop (outBase v30 v31 len : Word) (dstBytes : List Byte)
    (di m : Nat) (hm : m ≤ 8)
    (halign : outBase.toNat % 8 = 0)
    (hdlen : di + m ≤ dstBytes.length)
    (hover : outBase.toNat + (di + m) ≤ 2 ^ 64)
    (hvalid : ∀ k, k < m → isValidByteAccess (outBase + BitVec.ofNat 64 (di + k)) = true) :
    cpsTripleWithin (7 * m + 1) (rebBase + 224) (rebBase + 252) rebCode
      (((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 m - 1)) **
       ((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       ((.x6 : Reg) ↦ᵣ len) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outBase dstBytes)
      (((.x29 : Reg) ↦ᵣ (-1 : Word)) **
       ((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 (di + m))) **
       ((.x6 : Reg) ↦ᵣ len) ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outBase (writeShift dstBytes di len.toNat m)) := by
  have ha_t : (rebBase + 224) + signExtend13 (28 : BitVec 13) = rebBase + 252 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (rebBase + 224 : Word) + 4 = rebBase + 228 := by bv_omega
  induction m generalizing di dstBytes v30 v31 with
  | zero =>
    have hblt := blt_spec_gen_within .x29 .x0 (28 : BitVec 13)
      (BitVec.ofNat 64 0 - 1) (0 : Word) (rebBase + 224)
    rw [ha_t, ha_f] at hblt
    have hblt_framed := cpsBranchWithin_frameR
      (((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       ((.x6 : Reg) ↦ᵣ len) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion outBase dstBytes)
      (by pcFree) hblt
    have hblt_ext := cpsBranchWithin_extend_code (by rebmem 56) hblt_framed
    have htaken := cpsBranchWithin_takenPath hblt_ext (fun _ hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      refine ((sepConj_pure_right _).1 h_pure).2 ?_
      rw [lol_zero_cnt]
      exact slt_neg_one)
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) htaken
    · xperm_hyp hp
    · rw [lol_zero_cnt] at hq
      simp only [Nat.add_zero, writeShift_zero]
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (regIs_implies_regOwn .x30)
          (sepConj_mono_left (regIs_implies_regOwn .x31))))) h hq1
      xperm_hyp hq2
  | succ k ih =>
    have hcnt : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k :=
      ofNat_succ_sub_one k
    have hblt := blt_spec_gen_within .x29 .x0 (28 : BitVec 13)
      (BitVec.ofNat 64 (k + 1) - 1) (0 : Word) (rebBase + 224)
    rw [ha_t, ha_f, hcnt] at hblt
    have hblt_framed := cpsBranchWithin_frameR
      (((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       ((.x6 : Reg) ↦ᵣ len) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion outBase dstBytes)
      (by pcFree) hblt
    have hblt_ext := cpsBranchWithin_extend_code (by rebmem 56) hblt_framed
    have hnt := cpsBranchWithin_ntakenPath hblt_ext (fun _ hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      have hslt := ((sepConj_pure_right _).1 h_pure).2
      rw [slt_small_false k (by omega)] at hslt
      exact absurd hslt (by simp))
    have hA1 : cpsTripleWithin 1 (rebBase + 224) (rebBase + 228) rebCode
        ((((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 (k + 1) - 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
          (((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
           ((.x6 : Reg) ↦ᵣ len) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
           bytesRegion outBase dstBytes))
        (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x30 : Reg) ↦ᵣ v30) **
         ((.x31 : Reg) ↦ᵣ v31) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
         bytesRegion outBase dstBytes ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
      rw [hcnt]
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) hnt
    have hdi0 : di < dstBytes.length := by omega
    have body := rebLolBody outBase v30 v31 len dstBytes di k (by omega)
      halign hdi0 (by omega)
      (by have := hvalid 0 (by omega); simpa using this)
    have body_x0 := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (rebBase + 248)
    rw [lol_jal_back] at hjal
    have hjal_ext := cpsTripleWithin_extend_code (by rebmem 62) hjal
    have hjal_S := cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        (((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 k - 1)) **
         ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * k)) **
         ((.x31 : Reg) ↦ᵣ (len >>> (8 * k))) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x7 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 (di + 1))) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outBase
           (dstBytes.set di (BitVec.ofNat 8 (len.toNat / 256 ^ k % 256))))
        (by pcFree) hjal_ext)
    have hvalid' : ∀ j, j < k →
        isValidByteAccess (outBase + BitVec.ofNat 64 ((di + 1) + j)) = true := by
      intro j hj
      have h := hvalid (j + 1) (by omega)
      rwa [show di + (j + 1) = (di + 1) + j from by omega] at h
    have ihspec := ih
      (dstBytes := dstBytes.set di (BitVec.ofNat 8 (len.toNat / 256 ^ k % 256)))
      (di := di + 1) (v30 := BitVec.ofNat 64 (8 * k)) (v31 := len >>> (8 * k))
      (hm := by omega)
      (hdlen := by rw [List.length_set]; omega)
      (hover := by rw [show (di + 1) + k = di + (k + 1) from by omega]; omega)
      (hvalid := hvalid')
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA1 body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show di + (k + 1) = (di + 1) + k from by omega,
        writeShift_succ]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s1234

/-! ## §3  The short-path payload copy loop ([19]-[25])

    Port of `reubCopyLoop` — same six-instruction body, registers renamed:
    counter `x29`, source cursor `x5`, destination cursor `x7`, scratch `x28`. -/

set_option maxRecDepth 8000 in
/-- **One short-copy iteration** ([20]-[24], `rebBase+80 → rebBase+100`). -/
theorem rebShortCopyBody (srcBase dstBase v28 v29 : Word)
    (srcBytes dstBytes : List Byte) (si di : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsi : si < srcBytes.length) (hdi : di < dstBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64) (hdover : dstBase.toNat + di < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true)
    (hdvalid : isValidByteAccess (dstBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 (rebBase + 80) (rebBase + 100) rebCode
      (((.x28 : Reg) ↦ᵣ v28) ** ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** ((.x29 : Reg) ↦ᵣ v29) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (((.x28 : Reg) ↦ᵣ (srcBytes[si]'hsi).zeroExtend 64) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
       ((.x29 : Reg) ↦ᵣ (v29 + signExtend12 (-1 : BitVec 12))) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi))) := by
  have lbu := bytesRegion_lbu_within .x28 .x5 srcBase v28 (rebBase + 80) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  rw [show rebBase + 80 + 4 = rebBase + 84 from by bv_omega] at lbu
  have sb := bytesRegion_sb_within .x7 .x28 dstBase ((srcBytes[si]'hsi).zeroExtend 64)
    (rebBase + 84) dstBytes di hdalign hdi hdover hdvalid
  rw [show rebBase + 84 + 4 = rebBase + 88 from by bv_omega,
      truncate_zeroExtend_byte] at sb
  have a5 := addi_spec_gen_same_within .x5 (srcBase + BitVec.ofNat 64 si)
    (1 : BitVec 12) (rebBase + 88) (by nofun)
  rw [show rebBase + 88 + 4 = rebBase + 92 from by bv_omega, cur_up srcBase si] at a5
  have a7 := addi_spec_gen_same_within .x7 (dstBase + BitVec.ofNat 64 di)
    (1 : BitVec 12) (rebBase + 92) (by nofun)
  rw [show rebBase + 92 + 4 = rebBase + 96 from by bv_omega, cur_up dstBase di] at a7
  have a29 := addi_spec_gen_same_within .x29 v29 (-1 : BitVec 12) (rebBase + 96) (by nofun)
  rw [show rebBase + 96 + 4 = rebBase + 100 from by bv_omega] at a29
  runBlock lbu sb a5 a7 a29

set_option maxRecDepth 8000 in
/-- **The short-path payload copy loop** ([19]-[25], `rebBase+76 → rebBase+104`),
    by induction on the counter: `n` bytes move from `src[si..]` to `dst[di..]`
    in `7*n + 1` steps. -/
theorem rebShortCopyLoop (srcBase dstBase v28 : Word) (srcBytes dstBytes : List Byte)
    (si di n : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length) (hdlen : di + n ≤ dstBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hdover : dstBase.toNat + (di + n) ≤ 2 ^ 64) (hn : n < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true)
    (hdvalid : ∀ k, k < n → isValidByteAccess (dstBase + BitVec.ofNat 64 (di + k)) = true) :
    cpsTripleWithin (7 * n + 1) (rebBase + 76) (rebBase + 104) rebCode
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (((.x29 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + n))) **
       regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyN dstBytes srcBytes di si n)) := by
  have ha_t : (rebBase + 76) + signExtend13 (28 : BitVec 13) = rebBase + 104 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (rebBase + 76 : Word) + 4 = rebBase + 80 := by bv_omega
  induction n generalizing si di dstBytes v28 with
  | zero =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (rebBase + 76)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code (by rebmem 19) hbeq_framed
    have htaken := cpsBranchWithin_takenPath hbeq_ext (fun _ hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) htaken
    · xperm_hyp hp
    · rw [show (0#64 : Word) = 0 from by decide] at hq
      simp only [Nat.add_zero, copyN_zero]
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 := sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_implies_regOwn .x28)))) h hq1
      xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (rebBase + 76)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code (by rebmem 19) hbeq_framed
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) :=
      word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath hbeq_ext (fun _ hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hA1' : cpsTripleWithin 1 (rebBase + 76) (rebBase + 80) rebCode
        ((((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
          (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
           ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
           ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcBase srcBytes **
           bytesRegion dstBase dstBytes))
        (((.x28 : Reg) ↦ᵣ v28) ** ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
         ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes **
         ((.x0 : Reg) ↦ᵣ (0 : Word))) :=
      cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) hA1
    have hsi0 : si < srcBytes.length := by omega
    have hdi0 : di < dstBytes.length := by omega
    have body := rebShortCopyBody srcBase dstBase v28 (BitVec.ofNat 64 (k + 1))
      srcBytes dstBytes si di hsalign hdalign hsi0 hdi0 (by omega) (by omega)
      (by have := hsvalid 0 (by omega); simpa using this)
      (by have := hdvalid 0 (by omega); simpa using this)
    rw [word_ofNat_succ_dec k] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (rebBase + 100)
    rw [short_jal_back] at hjal
    have hjal_ext := cpsTripleWithin_extend_code (by rebmem 25) hjal
    have hjal_S := cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        (((.x28 : Reg) ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
         ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
         ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0)))
        (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k →
        isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have hdvalid' : ∀ j, j < k →
        isValidByteAccess (dstBase + BitVec.ofNat 64 ((di + 1) + j)) = true := by
      intro j hj
      have h := hdvalid (j + 1) (by omega)
      rwa [show di + (j + 1) = (di + 1) + j from by omega] at h
    have ihspec := ih
      (si := si + 1) (di := di + 1)
      (dstBytes := dstBytes.set di (srcBytes[si]'hsi0))
      (v28 := (srcBytes[si]'hsi0).zeroExtend 64)
      (hslen := by omega)
      (hdlen := by rw [List.length_set]; omega)
      (hsover := by omega)
      (hdover := by rw [show (di + 1) + k = di + (k + 1) from by omega]; omega)
      (hn := by omega)
      (hsvalid := hsvalid') (hdvalid := hdvalid')
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA1' body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hbyte : (srcBytes[si]'hsi0) = getByteAt srcBytes si := by simp [getByteAt, hsi0]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega,
        show di + (k + 1) = (di + 1) + k from by omega,
        show copyN dstBytes srcBytes di si (k + 1)
           = copyN (dstBytes.set di (srcBytes[si]'hsi0)) srcBytes (di + 1) (si + 1) k from by
          rw [copyN_succ, ← hbyte]]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s1234

/-! ## §4  The long-path payload copy loop ([63]-[70])

    The same six instructions as §3, scratching `x30` instead of `x28` — because
    `x28` still holds `bc`, which [71] needs.  `x28` is simply absent from this
    lemma; the composition frames it across. -/

set_option maxRecDepth 8000 in
/-- **One long-copy iteration** ([65]-[69], `rebBase+260 → rebBase+280`). -/
theorem rebLongCopyBody (srcBase dstBase v30 v29 : Word)
    (srcBytes dstBytes : List Byte) (si di : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsi : si < srcBytes.length) (hdi : di < dstBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64) (hdover : dstBase.toNat + di < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true)
    (hdvalid : isValidByteAccess (dstBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 (rebBase + 260) (rebBase + 280) rebCode
      (((.x30 : Reg) ↦ᵣ v30) ** ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** ((.x29 : Reg) ↦ᵣ v29) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (((.x30 : Reg) ↦ᵣ (srcBytes[si]'hsi).zeroExtend 64) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
       ((.x29 : Reg) ↦ᵣ (v29 + signExtend12 (-1 : BitVec 12))) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi))) := by
  have lbu := bytesRegion_lbu_within .x30 .x5 srcBase v30 (rebBase + 260) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  rw [show rebBase + 260 + 4 = rebBase + 264 from by bv_omega] at lbu
  have sb := bytesRegion_sb_within .x7 .x30 dstBase ((srcBytes[si]'hsi).zeroExtend 64)
    (rebBase + 264) dstBytes di hdalign hdi hdover hdvalid
  rw [show rebBase + 264 + 4 = rebBase + 268 from by bv_omega,
      truncate_zeroExtend_byte] at sb
  have a5 := addi_spec_gen_same_within .x5 (srcBase + BitVec.ofNat 64 si)
    (1 : BitVec 12) (rebBase + 268) (by nofun)
  rw [show rebBase + 268 + 4 = rebBase + 272 from by bv_omega, cur_up srcBase si] at a5
  have a7 := addi_spec_gen_same_within .x7 (dstBase + BitVec.ofNat 64 di)
    (1 : BitVec 12) (rebBase + 272) (by nofun)
  rw [show rebBase + 272 + 4 = rebBase + 276 from by bv_omega, cur_up dstBase di] at a7
  have a29 := addi_spec_gen_same_within .x29 v29 (-1 : BitVec 12) (rebBase + 276) (by nofun)
  rw [show rebBase + 276 + 4 = rebBase + 280 from by bv_omega] at a29
  runBlock lbu sb a5 a7 a29

set_option maxRecDepth 8000 in
/-- **The long-path payload copy loop** ([64]-[70], `rebBase+256 → rebBase+284`),
    by induction on the counter: `7*n + 1` steps. -/
theorem rebLongCopyLoop (srcBase dstBase v30 : Word) (srcBytes dstBytes : List Byte)
    (si di n : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length) (hdlen : di + n ≤ dstBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hdover : dstBase.toNat + (di + n) ≤ 2 ^ 64) (hn : n < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true)
    (hdvalid : ∀ k, k < n → isValidByteAccess (dstBase + BitVec.ofNat 64 (di + k)) = true) :
    cpsTripleWithin (7 * n + 1) (rebBase + 256) (rebBase + 284) rebCode
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (((.x29 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + n))) **
       regOwn .x30 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyN dstBytes srcBytes di si n)) := by
  have ha_t : (rebBase + 256) + signExtend13 (28 : BitVec 13) = rebBase + 284 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (rebBase + 256 : Word) + 4 = rebBase + 260 := by bv_omega
  induction n generalizing si di dstBytes v30 with
  | zero =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (rebBase + 256)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code (by rebmem 64) hbeq_framed
    have htaken := cpsBranchWithin_takenPath hbeq_ext (fun _ hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) htaken
    · xperm_hyp hp
    · rw [show (0#64 : Word) = 0 from by decide] at hq
      simp only [Nat.add_zero, copyN_zero]
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 := sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_implies_regOwn .x30)))) h hq1
      xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (rebBase + 256)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code (by rebmem 64) hbeq_framed
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) :=
      word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath hbeq_ext (fun _ hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hA1' : cpsTripleWithin 1 (rebBase + 256) (rebBase + 260) rebCode
        ((((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
          (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
           ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
           ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcBase srcBytes **
           bytesRegion dstBase dstBytes))
        (((.x30 : Reg) ↦ᵣ v30) ** ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
         ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes **
         ((.x0 : Reg) ↦ᵣ (0 : Word))) :=
      cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) hA1
    have hsi0 : si < srcBytes.length := by omega
    have hdi0 : di < dstBytes.length := by omega
    have body := rebLongCopyBody srcBase dstBase v30 (BitVec.ofNat 64 (k + 1))
      srcBytes dstBytes si di hsalign hdalign hsi0 hdi0 (by omega) (by omega)
      (by have := hsvalid 0 (by omega); simpa using this)
      (by have := hdvalid 0 (by omega); simpa using this)
    rw [word_ofNat_succ_dec k] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (rebBase + 280)
    rw [long_jal_back] at hjal
    have hjal_ext := cpsTripleWithin_extend_code (by rebmem 70) hjal
    have hjal_S := cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        (((.x30 : Reg) ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
         ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         ((.x7 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
         ((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0)))
        (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k →
        isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have hdvalid' : ∀ j, j < k →
        isValidByteAccess (dstBase + BitVec.ofNat 64 ((di + 1) + j)) = true := by
      intro j hj
      have h := hdvalid (j + 1) (by omega)
      rwa [show di + (j + 1) = (di + 1) + j from by omega] at h
    have ihspec := ih
      (si := si + 1) (di := di + 1)
      (dstBytes := dstBytes.set di (srcBytes[si]'hsi0))
      (v30 := (srcBytes[si]'hsi0).zeroExtend 64)
      (hslen := by omega)
      (hdlen := by rw [List.length_set]; omega)
      (hsover := by omega)
      (hdover := by rw [show (di + 1) + k = di + (k + 1) from by omega]; omega)
      (hn := by omega)
      (hsvalid := hsvalid') (hdvalid := hdvalid')
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA1' body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hbyte : (srcBytes[si]'hsi0) = getByteAt srcBytes si := by simp [getByteAt, hsi0]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega,
        show di + (k + 1) = (di + 1) + k from by omega,
        show copyN dstBytes srcBytes di si (k + 1)
           = copyN (dstBytes.set di (srcBytes[si]'hsi0)) srcBytes (di + 1) (si + 1) k from by
          rw [copyN_succ, ← hbyte]]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s1234

/-! ## §5  Guards for the two data-driven branches

    The raw-byte probe compares the loaded byte against `0x80`, and the
    dispatch compares the length against 56.  Same shapes as item 1's
    `ult_zeroExtend_of_lt`/`_of_ge`, which are `private` there. -/

/-- `[7]`'s guard, below the boundary: a byte under `0x80` falls through. -/
private theorem ult_zx_128_lt (b : Byte) (h : b.toNat < 128) :
    BitVec.ult (b.zeroExtend 64) (128 : Word) = true := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_setWidth,
    show (128 : Word).toNat = 128 from by decide]
  omega

/-- `[7]`'s guard, at or above the boundary. -/
private theorem ult_zx_128_ge (b : Byte) (h : 128 ≤ b.toNat) :
    BitVec.ult (b.zeroExtend 64) (128 : Word) = false := by
  have hb : b.toNat < 2 ^ 8 := b.isLt
  simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_setWidth,
    show (128 : Word).toNat = 128 from by decide]
  omega

/-- `[14]`'s guard, short side: a length below 56 falls through. -/
private theorem ult_56_lt (len : Word) (h : len.toNat < 56) :
    BitVec.ult len (56 : Word) = true := by
  simp only [BitVec.ult, decide_eq_true_eq,
    show (56 : Word).toNat = 56 from by decide]
  omega

/-- `[14]`'s guard, long side. -/
private theorem ult_56_ge (len : Word) (h : 56 ≤ len.toNat) :
    BitVec.ult len (56 : Word) = false := by
  simp only [BitVec.ult, decide_eq_false_iff_not,
    show (56 : Word).toNat = 56 from by decide]
  omega

/-! ## §6  The prologue ([0]-[4]), one lemma per exit

    Straight-line triples rather than one branch, so the composition splits on
    the *data* first — the discipline that keeps every path a `runBlock` chain. -/

set_option maxRecDepth 8000 in
/-- **Prologue, `len ≠ 1`** ([0]-[4], `BNE` taken): to the dispatch at `+52`. -/
theorem rebPrologueNe1 (srcPtr outPtr len v5 v6 v7 v28 : Word)
    (hne : len ≠ (1 : Word)) :
    cpsTripleWithin 5 rebBase (rebBase + 52) rebCode
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28))
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
       ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ outPtr) **
       ((.x28 : Reg) ↦ᵣ (1 : Word))) := by
  have h5 := mv_spec_gen_within .x5 .x10 srcPtr v5 rebBase (by decide)
  rw [show rebBase + 4 = rebBase + 4 from rfl] at h5
  have h6 := mv_spec_gen_within .x6 .x11 len v6 (rebBase + 4) (by decide)
  rw [show rebBase + 4 + 4 = rebBase + 8 from by bv_omega] at h6
  have h7 := mv_spec_gen_within .x7 .x12 outPtr v7 (rebBase + 8) (by decide)
  rw [show rebBase + 8 + 4 = rebBase + 12 from by bv_omega] at h7
  have hli := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 12) (by decide)
  rw [show rebBase + 12 + 4 = rebBase + 16 from by bv_omega] at hli
  have hb0 := bne_spec_gen_within .x6 .x28 (36 : BitVec 13) len (1 : Word) (rebBase + 16)
  rw [show rebBase + 16 + signExtend13 (36 : BitVec 13) = rebBase + 52 from by
        rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]
        bv_omega] at hb0
  have hb := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb0 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      exact hne ((sepConj_pure_right _).1 hpure).2))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 5 rebBase (rebBase + 52) rebCode
        (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x11 : Reg) ↦ᵣ len) ** ((.x6 : Reg) ↦ᵣ v6) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x28 : Reg) ↦ᵣ v28))
        (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
         ((.x11 : Reg) ↦ᵣ len) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x7 : Reg) ↦ᵣ outPtr) **
         ((.x28 : Reg) ↦ᵣ (1 : Word))) from by
      (runBlock h5 h6 h7 hli hb))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **Prologue, `len = 1`** ([0]-[4], `BNE` falls through): to the raw-byte
    probe at `+20`. -/
theorem rebPrologueEq1 (srcPtr outPtr len v5 v6 v7 v28 : Word)
    (heq : len = (1 : Word)) :
    cpsTripleWithin 5 rebBase (rebBase + 20) rebCode
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28))
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ len) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
       ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ outPtr) **
       ((.x28 : Reg) ↦ᵣ (1 : Word))) := by
  have h5 := mv_spec_gen_within .x5 .x10 srcPtr v5 rebBase (by decide)
  have h6 := mv_spec_gen_within .x6 .x11 len v6 (rebBase + 4) (by decide)
  rw [show rebBase + 4 + 4 = rebBase + 8 from by bv_omega] at h6
  have h7 := mv_spec_gen_within .x7 .x12 outPtr v7 (rebBase + 8) (by decide)
  rw [show rebBase + 8 + 4 = rebBase + 12 from by bv_omega] at h7
  have hli := li_spec_gen_within .x28 v28 (1 : Word) (rebBase + 12) (by decide)
  rw [show rebBase + 12 + 4 = rebBase + 16 from by bv_omega] at hli
  have hb0 := bne_spec_gen_within .x6 .x28 (36 : BitVec 13) len (1 : Word) (rebBase + 16)
  rw [show rebBase + 16 + 4 = rebBase + 20 from by bv_omega] at hb0
  have hb := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb0 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      exact absurd heq ((sepConj_pure_right _).1 hpure).2))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 5 rebBase (rebBase + 20) rebCode
        (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x11 : Reg) ↦ᵣ len) ** ((.x6 : Reg) ↦ᵣ v6) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x28 : Reg) ↦ᵣ v28))
        (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
         ((.x11 : Reg) ↦ᵣ len) ** ((.x6 : Reg) ↦ᵣ len) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x7 : Reg) ↦ᵣ outPtr) **
         ((.x28 : Reg) ↦ᵣ (1 : Word))) from by
      (runBlock h5 h6 h7 hli hb))
  · xperm_hyp hp
  · xperm_hyp hp

/-! ## §7  The raw-byte probe ([5]-[7]), one lemma per exit -/

set_option maxRecDepth 8000 in
/-- **Probe, byte below `0x80`** ([5]-[7], `BGEU` falls through): to the raw
    tail at `+32`. -/
theorem rebRawProbeSmall (srcPtr v29 v30 : Word) (srcBytes : List Byte)
    (h0 : 0 < srcBytes.length)
    (hsmall : (srcBytes[0]'h0).toNat < 128)
    (hsalign : srcPtr.toNat % 8 = 0) (hsover : srcPtr.toNat < 2 ^ 64)
    (hsvalid : isValidByteAccess srcPtr = true) :
    cpsTripleWithin 3 (rebBase + 20) (rebBase + 32) rebCode
      (((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcPtr srcBytes)
      (((.x5 : Reg) ↦ᵣ srcPtr) **
       ((.x29 : Reg) ↦ᵣ (srcBytes[0]'h0).zeroExtend 64) **
       ((.x30 : Reg) ↦ᵣ (128 : Word)) ** bytesRegion srcPtr srcBytes) := by
  have haddr0 : srcPtr + BitVec.ofNat 64 0 = srcPtr := by bv_omega
  have hlbu := bytesRegion_lbu_within .x29 .x5 srcPtr v29 (rebBase + 20) srcBytes 0
    (by decide) hsalign h0 (by omega) (by rw [haddr0]; exact hsvalid)
  rw [show rebBase + 20 + 4 = rebBase + 24 from by bv_omega, haddr0] at hlbu
  have hli := li_spec_gen_within .x30 v30 (128 : Word) (rebBase + 24) (by decide)
  rw [show rebBase + 24 + 4 = rebBase + 28 from by bv_omega] at hli
  have hb0 := bgeu_spec_gen_within .x29 .x30 (24 : BitVec 13)
    ((srcBytes[0]'h0).zeroExtend 64) (128 : Word) (rebBase + 28)
  rw [show rebBase + 28 + 4 = rebBase + 32 from by bv_omega] at hb0
  have hb := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb0 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hnu := ((sepConj_pure_right _).1 hpure).2
      rw [ult_zx_128_lt _ hsmall] at hnu
      exact absurd hnu (by simp)))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 3 (rebBase + 20) (rebBase + 32) rebCode
        (((.x29 : Reg) ↦ᵣ v29) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
         bytesRegion srcPtr srcBytes ** ((.x30 : Reg) ↦ᵣ v30))
        (((.x29 : Reg) ↦ᵣ (srcBytes[0]'h0).zeroExtend 64) **
         ((.x5 : Reg) ↦ᵣ srcPtr) ** bytesRegion srcPtr srcBytes **
         ((.x30 : Reg) ↦ᵣ (128 : Word))) from by
      (runBlock hlbu hli hb))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **Probe, byte at or above `0x80`** ([5]-[7], `BGEU` taken): to the dispatch
    at `+52` — a one-byte string that still takes the `0x81` short header. -/
theorem rebRawProbeLarge (srcPtr v29 v30 : Word) (srcBytes : List Byte)
    (h0 : 0 < srcBytes.length)
    (hlarge : 128 ≤ (srcBytes[0]'h0).toNat)
    (hsalign : srcPtr.toNat % 8 = 0) (hsover : srcPtr.toNat < 2 ^ 64)
    (hsvalid : isValidByteAccess srcPtr = true) :
    cpsTripleWithin 3 (rebBase + 20) (rebBase + 52) rebCode
      (((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcPtr srcBytes)
      (((.x5 : Reg) ↦ᵣ srcPtr) **
       ((.x29 : Reg) ↦ᵣ (srcBytes[0]'h0).zeroExtend 64) **
       ((.x30 : Reg) ↦ᵣ (128 : Word)) ** bytesRegion srcPtr srcBytes) := by
  have haddr0 : srcPtr + BitVec.ofNat 64 0 = srcPtr := by bv_omega
  have hlbu := bytesRegion_lbu_within .x29 .x5 srcPtr v29 (rebBase + 20) srcBytes 0
    (by decide) hsalign h0 (by omega) (by rw [haddr0]; exact hsvalid)
  rw [show rebBase + 20 + 4 = rebBase + 24 from by bv_omega, haddr0] at hlbu
  have hli := li_spec_gen_within .x30 v30 (128 : Word) (rebBase + 24) (by decide)
  rw [show rebBase + 24 + 4 = rebBase + 28 from by bv_omega] at hli
  have hb0 := bgeu_spec_gen_within .x29 .x30 (24 : BitVec 13)
    ((srcBytes[0]'h0).zeroExtend 64) (128 : Word) (rebBase + 28)
  rw [show rebBase + 28 + signExtend13 (24 : BitVec 13) = rebBase + 52 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]
        bv_omega] at hb0
  have hb := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb0 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hu := ((sepConj_pure_right _).1 hpure).2
      rw [ult_zx_128_ge _ hlarge] at hu
      exact absurd hu (by simp)))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 3 (rebBase + 20) (rebBase + 52) rebCode
        (((.x29 : Reg) ↦ᵣ v29) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
         bytesRegion srcPtr srcBytes ** ((.x30 : Reg) ↦ᵣ v30))
        (((.x29 : Reg) ↦ᵣ (srcBytes[0]'h0).zeroExtend 64) **
         ((.x5 : Reg) ↦ᵣ srcPtr) ** bytesRegion srcPtr srcBytes **
         ((.x30 : Reg) ↦ᵣ (128 : Word))) from by
      (runBlock hlbu hli hb))
  · xperm_hyp hp
  · xperm_hyp hp

/-! ## §8  The three tails and the two dispatch arms

    Each tail ends `LI a0, 0; JALR x0, x1, 0` — status zero, always: the
    routine is total, and each tail also writes the length dword at `*a3`. -/

set_option maxRecDepth 8000 in
/-- **The raw-byte tail** ([8]-[12], `rebBase+32 → ra &&& ~~~1`): store the
    byte unprefixed and report one byte written. -/
theorem rebRawTail (outPtr cellPtr raVal cellOld v31 v10 : Word) (b : Byte)
    (outBytes : List Byte)
    (holen : 0 < outBytes.length)
    (hoalign : outPtr.toNat % 8 = 0) (hoover : outPtr.toNat < 2 ^ 64)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin 5 (rebBase + 32) (raVal &&& ~~~1) rebCode
      (((.x29 : Reg) ↦ᵣ b.zeroExtend 64) ** ((.x7 : Reg) ↦ᵣ outPtr) **
       ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ cellOld) **
       ((.x31 : Reg) ↦ᵣ v31) ** ((.x10 : Reg) ↦ᵣ v10) **
       ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion outPtr outBytes)
      (((.x29 : Reg) ↦ᵣ b.zeroExtend 64) ** ((.x7 : Reg) ↦ᵣ outPtr) **
       ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ (1 : Word)) **
       ((.x31 : Reg) ↦ᵣ (1 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raVal) **
       bytesRegion outPtr (outBytes.set 0 b)) := by
  have haddr0 : outPtr + BitVec.ofNat 64 0 = outPtr := by bv_omega
  have hsb := bytesRegion_sb_within .x7 .x29 outPtr (b.zeroExtend 64)
    (rebBase + 32) outBytes 0 hoalign holen (by omega)
    (by rw [haddr0]; exact hovalid)
  rw [show rebBase + 32 + 4 = rebBase + 36 from by bv_omega, haddr0,
      truncate_zeroExtend_byte] at hsb
  have hli31 := li_spec_gen_within .x31 v31 (1 : Word) (rebBase + 36) (by decide)
  rw [show rebBase + 36 + 4 = rebBase + 40 from by bv_omega] at hli31
  have hsd := sd_spec_gen_within .x13 .x31 cellPtr (1 : Word) cellOld
    (0 : BitVec 12) (rebBase + 40)
  rw [show rebBase + 40 + 4 = rebBase + 44 from by bv_omega,
      show cellPtr + signExtend12 (0 : BitVec 12) = cellPtr from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hsd
  have hli10 := li_spec_gen_within .x10 v10 (0 : Word) (rebBase + 44) (by decide)
  rw [show rebBase + 44 + 4 = rebBase + 48 from by bv_omega] at hli10
  have hret := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (rebBase + 48)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 5 (rebBase + 32) (raVal &&& ~~~1) rebCode
        (((.x7 : Reg) ↦ᵣ outPtr) ** ((.x29 : Reg) ↦ᵣ b.zeroExtend 64) **
         bytesRegion outPtr outBytes ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ cellOld) **
         ((.x10 : Reg) ↦ᵣ v10) ** ((.x1 : Reg) ↦ᵣ raVal))
        (((.x7 : Reg) ↦ᵣ outPtr) ** ((.x29 : Reg) ↦ᵣ b.zeroExtend 64) **
         bytesRegion outPtr (outBytes.set 0 b) ** ((.x31 : Reg) ↦ᵣ (1 : Word)) **
         ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ (1 : Word)) **
         ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal)) from by
      (runBlock hsb hli31 hsd hli10 hret))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **Dispatch, short side** ([13]-[14], `BGEU` falls through): `len < 56`. -/
theorem rebDispatchShort (len v28 : Word) (hlt : len.toNat < 56) :
    cpsTripleWithin 2 (rebBase + 52) (rebBase + 60) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28))
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (56 : Word))) := by
  have hli := li_spec_gen_within .x28 v28 (56 : Word) (rebBase + 52) (by decide)
  rw [show rebBase + 52 + 4 = rebBase + 56 from by bv_omega] at hli
  have hb0 := bgeu_spec_gen_within .x6 .x28 (64 : BitVec 13) len (56 : Word)
    (rebBase + 56)
  rw [show rebBase + 56 + 4 = rebBase + 60 from by bv_omega] at hb0
  have hb := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hb0 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have hnu := ((sepConj_pure_right _).1 hpure).2
      rw [ult_56_lt len hlt] at hnu
      exact absurd hnu (by simp)))
  runBlock hli hb

set_option maxRecDepth 8000 in
/-- **Dispatch, long side** ([13]-[14], `BGEU` taken): `len ≥ 56`, to the `bc`
    ladder at `+120`. -/
theorem rebDispatchLong (len v28 : Word) (hge : 56 ≤ len.toNat) :
    cpsTripleWithin 2 (rebBase + 52) (rebBase + 120) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ v28))
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (56 : Word))) := by
  have hli := li_spec_gen_within .x28 v28 (56 : Word) (rebBase + 52) (by decide)
  rw [show rebBase + 52 + 4 = rebBase + 56 from by bv_omega] at hli
  have hb0 := bgeu_spec_gen_within .x6 .x28 (64 : BitVec 13) len (56 : Word)
    (rebBase + 56)
  rw [show rebBase + 56 + signExtend13 (64 : BitVec 13) = rebBase + 120 from by
        rw [show signExtend13 (64 : BitVec 13) = (64 : Word) from by decide]
        bv_omega] at hb0
  have hb := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hb0 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have hu := ((sepConj_pure_right _).1 hpure).2
      rw [ult_56_ge len hge] at hu
      exact absurd hu (by simp)))
  runBlock hli hb

set_option maxRecDepth 8000 in
/-- **The short header** ([15]-[18], `rebBase+60 → rebBase+76`): write
    `0x80 + len` and set up the copy loop. -/
theorem rebShortHeader (outPtr len v29 : Word) (outBytes : List Byte)
    (holen : 0 < outBytes.length)
    (hoalign : outPtr.toNat % 8 = 0) (hoover : outPtr.toNat < 2 ^ 64)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin 4 (rebBase + 60) (rebBase + 76) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (56 : Word)) **
       ((.x7 : Reg) ↦ᵣ outPtr) ** ((.x29 : Reg) ↦ᵣ v29) **
       bytesRegion outPtr outBytes)
      (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (len + 128)) **
       ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) ** ((.x29 : Reg) ↦ᵣ len) **
       bytesRegion outPtr (outBytes.set 0 ((len + 128).truncate 8))) := by
  have haddr0 : outPtr + BitVec.ofNat 64 0 = outPtr := by bv_omega
  have haddi := addi_spec_gen_within .x28 .x6 (56 : Word) len (128 : BitVec 12)
    (rebBase + 60) (by decide)
  rw [show rebBase + 60 + 4 = rebBase + 64 from by bv_omega,
      show signExtend12 (128 : BitVec 12) = (128 : Word) from by decide] at haddi
  have hsb := bytesRegion_sb_within .x7 .x28 outPtr (len + 128)
    (rebBase + 64) outBytes 0 hoalign holen (by omega)
    (by rw [haddr0]; exact hovalid)
  rw [show rebBase + 64 + 4 = rebBase + 68 from by bv_omega, haddr0] at hsb
  have ha7 := addi_spec_gen_same_within .x7 outPtr (1 : BitVec 12)
    (rebBase + 68) (by nofun)
  rw [show rebBase + 68 + 4 = rebBase + 72 from by bv_omega,
      show outPtr + signExtend12 (1 : BitVec 12) = outPtr + BitVec.ofNat 64 1 from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega] at ha7
  have hmv := mv_spec_gen_within .x29 .x6 len v29 (rebBase + 72) (by decide)
  rw [show rebBase + 72 + 4 = rebBase + 76 from by bv_omega] at hmv
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 4 (rebBase + 60) (rebBase + 76) rebCode
        (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (56 : Word)) **
         ((.x7 : Reg) ↦ᵣ outPtr) ** bytesRegion outPtr outBytes **
         ((.x29 : Reg) ↦ᵣ v29))
        (((.x6 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (len + 128)) **
         ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
         bytesRegion outPtr (outBytes.set 0 ((len + 128).truncate 8)) **
         ((.x29 : Reg) ↦ᵣ len)) from by
      (runBlock haddi hsb ha7 hmv))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **The short tail** ([26]-[29], `rebBase+104 → ra &&& ~~~1`): report
    `len + 1` bytes written. -/
theorem rebShortTail (cellPtr raVal cellOld len v31 v10 : Word) :
    cpsTripleWithin 4 (rebBase + 104) (raVal &&& ~~~1) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       (cellPtr ↦ₘ cellOld) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x1 : Reg) ↦ᵣ raVal))
      (((.x6 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
       (cellPtr ↦ₘ (len + 1)) ** ((.x31 : Reg) ↦ᵣ (len + 1)) **
       ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal)) := by
  have haddi := addi_spec_gen_within .x31 .x6 v31 len (1 : BitVec 12)
    (rebBase + 104) (by decide)
  rw [show rebBase + 104 + 4 = rebBase + 108 from by bv_omega,
      show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at haddi
  have hsd := sd_spec_gen_within .x13 .x31 cellPtr (len + 1) cellOld
    (0 : BitVec 12) (rebBase + 108)
  rw [show rebBase + 108 + 4 = rebBase + 112 from by bv_omega,
      show cellPtr + signExtend12 (0 : BitVec 12) = cellPtr from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hsd
  have hli := li_spec_gen_within .x10 v10 (0 : Word) (rebBase + 112) (by decide)
  rw [show rebBase + 112 + 4 = rebBase + 116 from by bv_omega] at hli
  have hret := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (rebBase + 116)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 4 (rebBase + 104) (raVal &&& ~~~1) rebCode
        (((.x6 : Reg) ↦ᵣ len) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ cellOld) **
         ((.x10 : Reg) ↦ᵣ v10) ** ((.x1 : Reg) ↦ᵣ raVal))
        (((.x6 : Reg) ↦ᵣ len) ** ((.x31 : Reg) ↦ᵣ (len + 1)) **
         ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ (len + 1)) **
         ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal)) from by
      (runBlock haddi hsd hli hret))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **The long header** ([52]-[55], `rebBase+208 → rebBase+224`): write
    `0xb7 + bc` and seed the length-of-length loop's counter with `bc - 1`. -/
theorem rebLongHeader (outPtr bcW v29 : Word) (outBytes : List Byte)
    (holen : 0 < outBytes.length)
    (hoalign : outPtr.toNat % 8 = 0) (hoover : outPtr.toNat < 2 ^ 64)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin 4 (rebBase + 208) (rebBase + 224) rebCode
      (((.x28 : Reg) ↦ᵣ bcW) ** ((.x7 : Reg) ↦ᵣ outPtr) **
       ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion outPtr outBytes)
      (((.x28 : Reg) ↦ᵣ bcW) **
       ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
       ((.x29 : Reg) ↦ᵣ (bcW - 1)) **
       bytesRegion outPtr (outBytes.set 0 ((bcW + 183).truncate 8))) := by
  have haddr0 : outPtr + BitVec.ofNat 64 0 = outPtr := by bv_omega
  have haddi := addi_spec_gen_within .x29 .x28 v29 bcW (183 : BitVec 12)
    (rebBase + 208) (by decide)
  rw [show rebBase + 208 + 4 = rebBase + 212 from by bv_omega,
      show signExtend12 (183 : BitVec 12) = (183 : Word) from by decide] at haddi
  have hsb := bytesRegion_sb_within .x7 .x29 outPtr (bcW + 183)
    (rebBase + 212) outBytes 0 hoalign holen (by omega)
    (by rw [haddr0]; exact hovalid)
  rw [show rebBase + 212 + 4 = rebBase + 216 from by bv_omega, haddr0] at hsb
  have ha7 := addi_spec_gen_same_within .x7 outPtr (1 : BitVec 12)
    (rebBase + 216) (by nofun)
  rw [show rebBase + 216 + 4 = rebBase + 220 from by bv_omega,
      show outPtr + signExtend12 (1 : BitVec 12) = outPtr + BitVec.ofNat 64 1 from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega] at ha7
  have ha29 := addi_spec_gen_within .x29 .x28 (bcW + 183) bcW (-1 : BitVec 12)
    (rebBase + 220) (by decide)
  rw [show rebBase + 220 + 4 = rebBase + 224 from by bv_omega,
      cnt_dec bcW] at ha29
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 4 (rebBase + 208) (rebBase + 224) rebCode
        (((.x28 : Reg) ↦ᵣ bcW) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x7 : Reg) ↦ᵣ outPtr) ** bytesRegion outPtr outBytes)
        (((.x28 : Reg) ↦ᵣ bcW) ** ((.x29 : Reg) ↦ᵣ (bcW - 1)) **
         ((.x7 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
         bytesRegion outPtr (outBytes.set 0 ((bcW + 183).truncate 8))) from by
      (runBlock haddi hsb ha7 ha29))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **The long-copy setup** ([63], `rebBase+252 → rebBase+256`): reload the
    payload counter. -/
theorem rebLongCopySetup (len v29 : Word) :
    cpsTripleWithin 1 (rebBase + 252) (rebBase + 256) rebCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x29 : Reg) ↦ᵣ v29))
      (((.x6 : Reg) ↦ᵣ len) ** ((.x29 : Reg) ↦ᵣ len)) := by
  have hmv := mv_spec_gen_within .x29 .x6 len v29 (rebBase + 252) (by decide)
  rw [show rebBase + 252 + 4 = rebBase + 256 from by bv_omega] at hmv
  runBlock hmv

set_option maxRecDepth 8000 in
/-- **The long tail** ([71]-[75], `rebBase+284 → ra &&& ~~~1`): report
    `bc + 1 + len` bytes written — header, length-of-length, payload.  `x28`
    still holds `bc` here, which is why the long copy loop scratched `x30`. -/
theorem rebLongTail (cellPtr raVal cellOld bcW len v30 v10 : Word) :
    cpsTripleWithin 5 (rebBase + 284) (raVal &&& ~~~1) rebCode
      (((.x28 : Reg) ↦ᵣ bcW) ** ((.x6 : Reg) ↦ᵣ len) **
       ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ cellOld) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x10 : Reg) ↦ᵣ v10) **
       ((.x1 : Reg) ↦ᵣ raVal))
      (((.x28 : Reg) ↦ᵣ bcW) ** ((.x6 : Reg) ↦ᵣ len) **
       ((.x13 : Reg) ↦ᵣ cellPtr) ** (cellPtr ↦ₘ (bcW + 1 + len)) **
       ((.x30 : Reg) ↦ᵣ (bcW + 1 + len)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ raVal)) := by
  have haddi := addi_spec_gen_within .x30 .x28 v30 bcW (1 : BitVec 12)
    (rebBase + 284) (by decide)
  rw [show rebBase + 284 + 4 = rebBase + 288 from by bv_omega,
      show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at haddi
  have hadd := add_spec_gen_rd_eq_rs1_within .x30 .x6 (bcW + 1) len
    (rebBase + 288) (by decide)
  rw [show rebBase + 288 + 4 = rebBase + 292 from by bv_omega] at hadd
  have hsd := sd_spec_gen_within .x13 .x30 cellPtr (bcW + 1 + len) cellOld
    (0 : BitVec 12) (rebBase + 292)
  rw [show rebBase + 292 + 4 = rebBase + 296 from by bv_omega,
      show cellPtr + signExtend12 (0 : BitVec 12) = cellPtr from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hsd
  have hli := li_spec_gen_within .x10 v10 (0 : Word) (rebBase + 296) (by decide)
  rw [show rebBase + 296 + 4 = rebBase + 300 from by bv_omega] at hli
  have hret := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (rebBase + 300)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 5 (rebBase + 284) (raVal &&& ~~~1) rebCode
        (((.x28 : Reg) ↦ᵣ bcW) ** ((.x30 : Reg) ↦ᵣ v30) **
         ((.x6 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
         (cellPtr ↦ₘ cellOld) ** ((.x10 : Reg) ↦ᵣ v10) **
         ((.x1 : Reg) ↦ᵣ raVal))
        (((.x28 : Reg) ↦ᵣ bcW) ** ((.x30 : Reg) ↦ᵣ (bcW + 1 + len)) **
         ((.x6 : Reg) ↦ᵣ len) ** ((.x13 : Reg) ↦ᵣ cellPtr) **
         (cellPtr ↦ₘ (bcW + 1 + len)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ raVal)) from by
      (runBlock haddi hadd hsd hli hret))
  · xperm_hyp hp
  · xperm_hyp hp

end RlpEncodeBytesSAsm

end EvmAsm.Codegen
