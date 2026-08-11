/-
  EvmAsm.Codegen.Programs.RlpEncodeListPrefixLoopSpec

  **`rlp_encode_list_prefix`'s length-byte loop, at a symbolic trip count** (GH #10780).

  ## The problem this removes

  `RlpEncodeListPrefixLong2Spec.lean:47-52` records the honest handoff for the
  `lenlen >= 3` arm: unrolling stops paying around `lenlen = 4`, the general arm wants
  the loop stated once with the invariant *"`out[1..k]` holds the top `k` bytes of `len`
  and `x29 = lenlen - 1 - k`"*, and otherwise the file grows by ~200 lines per byte.
  Six uncovered widths at that rate is ~1200 lines of unrolling.

  ⭐ **But that invariant already exists, and so does its machine proof.**
  `rlp_encode_bytes` has the *same* length-of-length loop, and `rebLolLoop`
  (`RlpEncodeBytesBlocksSAsm.lean:158`) proves it at a symbolic count with postcondition
  `writeShift dst di len.toNat m`. The two bodies are the same five instructions modulo
  a register renaming:

  | role | `rlp_encode_bytes` [57]-[61] | `rlp_encode_list_prefix` idx36-40 |
  |---|---|---|
  | counter (down) | `x29` | `x29` |
  | shift amount | `x30` | `x31` |
  | extracted byte | `x31` | `x5` |
  | value | `x6` | `x10` |
  | cursor (up) | `x7` | `x30` |

  Head `BLT x29, x0, +28`, back edge `JAL x0, -24`, exit at head+28 — identical on both
  sides. So this module is a **port**, in the same sense `rebShortCopyBody` is a port of
  `reubCopyLoop` (`RlpEncodeBytesBlocksSAsm.lean:283`, *"same six-instruction body,
  registers renamed"*). Porting loops across routines by renaming is established practice
  here; what is new is only that it had not been done in this direction.

  ## What this gives the remaining arms

  `lpLolLoop` is the reusable half. With it, each `lenlen` arm reduces to its ladder path
  through idx8-idx29 plus the fixed header/epilogue — mechanical per width, and the
  loop is proved once rather than once per byte.

  ⚠️ **Scope: the loop only.** No `lenlen >= 3` whole-arm triple is claimed here, and no
  registry row changes. The ladder dispatch is inherently eight cases (the routine
  computes `x28` by falling through `k` branches), so "unrolling stops paying" applies to
  the loop, not to the ladder — which is why the loop is the piece worth factoring out.

  The counter is **signed**: it runs `lenlen-1` down to `-1`, and the head `BLT` fires on
  `-1` (`slt_neg_one`) and falls through on `0..7` (`slt_small_false`). Both are reused
  from `RlpEncodeBytesSAsm`, along with `writeShift` and `ofNat_succ_sub_one`, rather
  than restated — the whole point being that the model side needs no new mathematics.

  ## ⭐ No `set_option maxRecDepth`

  `rebLolBody` and `rebLolLoop` each carry `set_option maxRecDepth 8000 in`. #10780 is
  explicit that a proof which only closes with a raised limit *"is a failure result here,
  not a pass"*, so the port was checked with the option removed rather than inherited
  along with the proof script: both theorems close at the default depth. Nothing here
  raises `maxRecDepth`, and no elaboration budget is widened anywhere in this module.
-/
import EvmAsm.Codegen.Programs.RlpEncodeBytesSAsm
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

namespace RlpEncodeListPrefixLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpEncodeBytesSAsm
  (writeShift writeShift_zero writeShift_succ slt_neg_one slt_small_false
   ofNat_succ_sub_one truncate_shift_eq u64ByteLen_eq_toBytesBE_length
   writeShift_eq_append beShift_eq_toBytesBE)
open EvmAsm.Codegen.RlpListEncodedSizeSAsm (u64ByteLen)

/-- Code-membership for a `∀ base` `ofProg` slice, as in the long1/long2 modules. It is
    `local` there and so not importable; re-declared rather than exported so nothing in
    those files changes. -/
local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr _ _ $k _ (by decide) (by decide) (by bv_omega)))

/-! ## Arithmetic helpers

    Re-declared from `RlpEncodeBytesBlocksSAsm.lean`, where they are `private`. Each is a
    one-line `decide`/`bv_omega` fact about the same instruction encodings, so the
    duplication is of statements, not of reasoning. -/

/-- `idx36 SLLI x31, x29, 3` at a counter below 8 is byte-scaling. -/
private theorem lp_slli (m : Nat) (h : m < 8) :
    BitVec.ofNat 64 m <<< (3 : BitVec 6).toNat = BitVec.ofNat 64 (8 * m) := by
  interval_cases m <;> decide

/-- `idx37 SRL`'s low-6-bit shift is exact: `8m ≤ 56 < 64`. -/
private theorem lp_srl_exp (m : Nat) (h : m < 8) :
    (BitVec.ofNat 64 (8 * m)).toNat % 64 = 8 * m := by
  rw [BitVec.toNat_ofNat]
  omega

/-- A decrement in the invariant's `- 1` form. Unconditional: `mod 2 ^ 64` absorbs it. -/
private theorem lp_cnt_dec (v : Word) :
    v + signExtend12 (-1 : BitVec 12) = v - 1 := by
  rw [show signExtend12 (-1 : BitVec 12) = -(1 : Word) from by decide]
  bv_omega

/-- A cursor advance by one byte. -/
private theorem lp_cur_up (base : Word) (i : Nat) :
    (base + BitVec.ofNat 64 i) + signExtend12 (1 : BitVec 12)
      = base + BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

/-- The exhausted counter reads as `-1`, which fires the exit `BLT`. -/
private theorem lp_zero_cnt : BitVec.ofNat 64 0 - 1 = (-1 : Word) := by decide

/-! ## The loop, at the routine's own addresses

    `idx35` (the head `BLT`) sits at `base + 140`; the body `idx36`-`idx40` runs
    `base + 144 → base + 164`; `idx41` is the back edge at `base + 164`, and the exit
    target is `base + 140 + 28 = base + 168` (`idx42`). These offsets are the reason the
    lemma cannot simply *be* `rebLolLoop`: that one is pinned to `rebBase + 224`. -/

/-- `idx41 JAL x0, -24` returns to the loop head. -/
private theorem lp_jal_back (base : Word) :
    (base + 164) + signExtend21 (-24 : BitVec 21) = base + 140 := by
  rw [show signExtend21 (-24 : BitVec 21) = -(24 : Word) from by decide]
  bv_omega

/-- **One length-byte iteration** (`idx36`-`idx40`, `base+144 → base+164`): at counter
    `m`, store big-endian byte `m` of `len` and step both cursors.

    Register roles are the renaming of `rebLolBody`'s given in this module's header. -/
theorem lpLolBody (base outBase v31 v5 len : Word) (dst : List Byte)
    (di m : Nat) (hm : m < 8)
    (halign : outBase.toNat % 8 = 0) (hdi : di < dst.length)
    (hover : outBase.toNat + di < 2 ^ 64)
    (hvalid : isValidByteAccess (outBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 (base + 144) (base + 164)
      (CodeReq.ofProg base rlpEncodeListPrefix_prog)
      (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 m) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       bytesRegion outBase dst)
      (((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 m - 1)) **
       ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * m)) **
       ((.x5 : Reg) ↦ᵣ (len >>> (8 * m))) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 (di + 1))) **
       bytesRegion outBase
         (dst.set di (BitVec.ofNat 8 (len.toNat / 256 ^ m % 256)))) := by
  set CR := CodeReq.ofProg base rlpEncodeListPrefix_prog with hCR
  -- idx36 (base+144): SLLI x31, x29, 3
  have hslli := liftCode (cr' := CR)
    (slli_spec_gen_within .x31 .x29 v31 (BitVec.ofNat 64 m) (3 : BitVec 6)
      (base + 144) (by decide))
    (by rw [hCR]; cmem 36)
  rw [show (base + 144 : Word) + 4 = base + 148 from by bv_omega, lp_slli m hm] at hslli
  -- idx37 (base+148): SRL x5, x10, x31
  have hsrl := liftCode (cr' := CR)
    (srl_spec_gen_within .x5 .x10 .x31 v5 len (BitVec.ofNat 64 (8 * m))
      (base + 148) (by decide))
    (by rw [hCR]; cmem 37)
  rw [show (base + 148 : Word) + 4 = base + 152 from by bv_omega,
      lp_srl_exp m hm] at hsrl
  -- idx38 (base+152): SB x30, x5, 0
  have hsb := liftCode (cr' := CR)
    (bytesRegion_sb_within .x30 .x5 outBase (len >>> (8 * m)) (base + 152) dst di
      halign hdi hover hvalid)
    (by rw [hCR]; cmem 38)
  rw [show (base + 152 : Word) + 4 = base + 156 from by bv_omega,
      truncate_shift_eq len m] at hsb
  -- idx39 (base+156): ADDI x30, x30, 1
  have ha30 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x30 (outBase + BitVec.ofNat 64 di) (1 : BitVec 12)
      (base + 156) (by nofun))
    (by rw [hCR]; cmem 39)
  rw [show (base + 156 : Word) + 4 = base + 160 from by bv_omega,
      lp_cur_up outBase di] at ha30
  -- idx40 (base+160): ADDI x29, x29, -1
  have ha29 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x29 (BitVec.ofNat 64 m) (-1 : BitVec 12)
      (base + 160) (by nofun))
    (by rw [hCR]; cmem 40)
  rw [show (base + 160 : Word) + 4 = base + 164 from by bv_omega,
      lp_cnt_dec (BitVec.ofNat 64 m)] at ha29
  runBlock hslli hsrl hsb ha30 ha29

/-- ⭐ **The length-byte loop at a symbolic trip count** (`idx35`-`idx41`,
    `base+140 → base+168`), by induction on the remaining count `m`: writes
    `writeShift dst di len.toNat m` in `7*m + 1` steps.

    This is the declaration the `lenlen >= 3` arms were missing. The invariant's counter
    is `ofNat 64 m - 1`: at `m = 0` that is `-1` and the signed `BLT` fires; at `m + 1` it
    is `ofNat m` and the guard falls through — sound because the counter never exceeds
    `lenlen - 1 ≤ 7`, which is what `hm` records. -/
theorem lpLolLoop (base outBase v31 v5 len : Word) (dstBytes : List Byte)
    (di m : Nat) (hm : m ≤ 8)
    (halign : outBase.toNat % 8 = 0)
    (hdlen : di + m ≤ dstBytes.length)
    (hover : outBase.toNat + (di + m) ≤ 2 ^ 64)
    (hvalid : ∀ k, k < m →
      isValidByteAccess (outBase + BitVec.ofNat 64 (di + k)) = true) :
    cpsTripleWithin (7 * m + 1) (base + 140) (base + 168)
      (CodeReq.ofProg base rlpEncodeListPrefix_prog)
      (((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 m - 1)) **
       ((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       ((.x10 : Reg) ↦ᵣ len) ** ((.x31 : Reg) ↦ᵣ v31) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outBase dstBytes)
      (((.x29 : Reg) ↦ᵣ (-1 : Word)) **
       ((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 (di + m))) **
       ((.x10 : Reg) ↦ᵣ len) ** regOwn .x31 ** regOwn .x5 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outBase (writeShift dstBytes di len.toNat m)) := by
  set CR := CodeReq.ofProg base rlpEncodeListPrefix_prog with hCR
  have ha_t : (base + 140 : Word) + signExtend13 (28 : BitVec 13) = base + 168 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 140 : Word) + 4 = base + 144 := by bv_omega
  induction m generalizing di dstBytes v31 v5 with
  | zero =>
    have hblt := blt_spec_gen_within .x29 .x0 (28 : BitVec 13)
      (BitVec.ofNat 64 0 - 1) (0 : Word) (base + 140)
    rw [ha_t, ha_f] at hblt
    have hblt_framed := cpsBranchWithin_frameR
      (((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       ((.x10 : Reg) ↦ᵣ len) ** ((.x31 : Reg) ↦ᵣ v31) ** ((.x5 : Reg) ↦ᵣ v5) **
       bytesRegion outBase dstBytes)
      (by pcFree) hblt
    have hblt_ext := cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by rw [hCR]; cmem 35) (h := hblt_framed)
    have htaken := cpsBranchWithin_takenPath hblt_ext (fun _ hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      refine ((sepConj_pure_right _).1 h_pure).2 ?_
      rw [lp_zero_cnt]
      exact slt_neg_one)
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) htaken
    · xperm_hyp hp
    · rw [lp_zero_cnt] at hq
      simp only [Nat.add_zero, writeShift_zero]
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (regIs_implies_regOwn .x31)
          (sepConj_mono_left (regIs_implies_regOwn .x5))))) h hq1
      xperm_hyp hq2
  | succ k ih =>
    have hcnt : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := ofNat_succ_sub_one k
    have hblt := blt_spec_gen_within .x29 .x0 (28 : BitVec 13)
      (BitVec.ofNat 64 (k + 1) - 1) (0 : Word) (base + 140)
    rw [ha_t, ha_f, hcnt] at hblt
    have hblt_framed := cpsBranchWithin_frameR
      (((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
       ((.x10 : Reg) ↦ᵣ len) ** ((.x31 : Reg) ↦ᵣ v31) ** ((.x5 : Reg) ↦ᵣ v5) **
       bytesRegion outBase dstBytes)
      (by pcFree) hblt
    have hblt_ext := cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by rw [hCR]; cmem 35) (h := hblt_framed)
    have hnt := cpsBranchWithin_ntakenPath hblt_ext (fun _ hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      have hslt := ((sepConj_pure_right _).1 h_pure).2
      rw [slt_small_false k (by omega)] at hslt
      exact absurd hslt (by simp))
    have hA1 : cpsTripleWithin 1 (base + 140) (base + 144) CR
        ((((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 (k + 1) - 1)) **
            ((.x0 : Reg) ↦ᵣ (0 : Word))) **
          (((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
           ((.x10 : Reg) ↦ᵣ len) ** ((.x31 : Reg) ↦ᵣ v31) ** ((.x5 : Reg) ↦ᵣ v5) **
           bytesRegion outBase dstBytes))
        (((.x29 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x5 : Reg) ↦ᵣ v5) ** ((.x10 : Reg) ↦ᵣ len) **
         ((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 di)) **
         bytesRegion outBase dstBytes ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
      rw [hcnt]
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) hnt
    have hdi0 : di < dstBytes.length := by omega
    have body := lpLolBody base outBase v31 v5 len dstBytes di k (by omega)
      halign hdi0 (by omega)
      (by have := hvalid 0 (by omega); simpa using this)
    have body_x0 := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 164)
    rw [lp_jal_back base] at hjal
    have hjal_ext := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by rw [hCR]; cmem 41) (h := hjal)
    have hjal_S := cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        (((.x29 : Reg) ↦ᵣ (BitVec.ofNat 64 k - 1)) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (8 * k)) **
         ((.x5 : Reg) ↦ᵣ (len >>> (8 * k))) ** ((.x10 : Reg) ↦ᵣ len) **
         ((.x30 : Reg) ↦ᵣ (outBase + BitVec.ofNat 64 (di + 1))) **
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
      (di := di + 1) (v31 := BitVec.ofNat 64 (8 * k)) (v5 := len >>> (8 * k))
      (hm := by omega)
      (hdlen := by rw [List.length_set]; omega)
      (hover := by rw [show (di + 1) + k = di + (k + 1) from by omega]; omega)
      (hvalid := hvalid')
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA1 body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) s123 ihspec
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show di + (k + 1) = (di + 1) + k from by omega,
        writeShift_succ]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s1234

/-! ## ⭐ What the loop writes, in reference terms

    At its own width the loop writes exactly the minimal big-endian encoding of `len` —
    `beShift_eq_toBytesBE` composed with `u64ByteLen_eq_toBytesBE_length`, both already
    proven. Stated here so a `lenlen >= 3` arm can name the reference directly instead of
    re-deriving the byte formula from `writeShift`. -/

/-- ⭐ **At the routine's own width the loop writes the minimal big-endian encoding**, and
    nothing else: the bytes before `di` and from `di + lenlen` on are untouched.

    So a `lenlen >= 3` arm can name `Nat.toBytesBE` — the reference — directly, instead of
    carrying `writeShift`'s per-index division formula through the composition. The frame
    halves (`take`/`drop`) are what make "and nothing else" part of the statement rather
    than a separate non-interference argument. -/
theorem lpLoop_writes_toBytesBE (dst : List Byte) (di : Nat) (len : Word)
    (hlen : di + u64ByteLen len ≤ dst.length) :
    writeShift dst di len.toNat (u64ByteLen len)
      = dst.take di ++ (Nat.toBytesBE len.toNat ++ dst.drop (di + u64ByteLen len)) := by
  rw [writeShift_eq_append _ _ _ _ hlen]
  congr 2
  rw [u64ByteLen_eq_toBytesBE_length]
  exact beShift_eq_toBytesBE len.toNat

end RlpEncodeListPrefixLoopSpec

end EvmAsm.Codegen
