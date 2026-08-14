/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegAbsorb

  **Pure multi-rate absorb model for `zkvm_keccak256_segments`.**

  The landed short-domain proof (`HashBridgeKeccakSegLoop` / `SegTop`) uses the
  coincidence `s4 = m` (global message index) ∧ sponge =
  `xorBytesUpTo keccakZeroStateBytes msg m`, which holds only while no
  mid-stream permute fires (`m ≤ 135`).

  This module names the general invariant the multi-rate machine path needs:

  * `kssFill m = m % 136` — rate-block fill after any completed permutes
  * `kssAbsorbed msg m` — sponge after absorbing the first `m` bytes:
    `keccakAbsorbedPrefix` of the completed blocks, then `keccakRemAbsorbed`
    of the residual into the rate (same pure vocabulary as `zkvm_keccak256`)

  Short-domain recovery (`m ≤ 135`) and the general SpecRef digest bridge
  (`keccakBodyDigest_eq_specref` at nonzero `N`) live here so the loop/top
  rewrite can import them without touching the machine composition yet.

  ## Scaffolding note

  `HashBridgeKeccakSegments.lean` carries a private byte-fold
  (`segmentsStateFold` / `segmentsFillAfter`) that already models fill wrap
  + mid-stream `keccakBytes`. Those defs are `private` and XOR byte-at-a-time
  into the rate; this module instead reuses the landed
  `keccakAbsorbedPrefix` / `keccakRemAbsorbed` stack so the digest bridge
  applies directly. The bytewise ↔ dword/CSRS bridge at a full rate block is
  `kssAbsorbed_succ_of_rate_csrs` (via `keccakPermuteAbsorbed_eq_byteXor`).
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakOuter
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTail
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBody
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTail

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-! ## Fill counter and absorbed sponge -/

/-- Rate-block fill after absorbing `m` bytes (post any mid-stream permutes). -/
def kssFill (m : Nat) : Nat := m % keccakAbsorbStep

theorem kssFill_lt (m : Nat) : kssFill m < keccakAbsorbStep :=
  Nat.mod_lt _ (by decide : 0 < keccakAbsorbStep)

theorem kssFill_of_le_rate (m : Nat) (hm : m < keccakAbsorbStep) :
    kssFill m = m :=
  Nat.mod_eq_of_lt hm

/-- Sponge image after absorbing the first `m` bytes of `msg`.

    Completed rate blocks go through `keccakAbsorbedPrefix`; the residual
    `m % 136` bytes are XOR-absorbed into the rate via `keccakRemAbsorbed`
    — the same decomposition `keccakBodyPrePad` uses for `zkvm_keccak256`. -/
def kssAbsorbed (msg : List (BitVec 8)) (m : Nat) : List (BitVec 8) :=
  let N := m / keccakAbsorbStep
  let rem := m % keccakAbsorbStep
  let stN := keccakAbsorbedPrefix msg N
  let tail := (msg.drop (keccakAbsorbStep * N)).take rem
  keccakRemAbsorbed stN tail rem

theorem kssAbsorbed_eq_bodyPrePad (msg : List (BitVec 8)) (m : Nat) :
    kssAbsorbed msg m =
      keccakBodyPrePad msg (m / keccakAbsorbStep) (m % keccakAbsorbStep) := by
  rfl

theorem kssAbsorbed_length (msg : List (BitVec 8)) (m : Nat) :
    (kssAbsorbed msg m).length = 200 := by
  simp only [kssAbsorbed, keccakRemAbsorbed]
  split_ifs <;> simp [xorBytesUpTo_length, keccakAbsorbedPrefix_length]

theorem kssAbsorbed_zero (msg : List (BitVec 8)) :
    kssAbsorbed msg 0 = keccakZeroStateBytes := by
  simp only [kssAbsorbed, keccakAbsorbStep, Nat.zero_div, Nat.zero_mod,
    keccakAbsorbedPrefix, keccakRemAbsorbed_zero]

/-- `xorBytesUpTo` depends only on the first `q` input bytes (via `getD`). -/
private theorem xorBytesUpTo_congr_prefix (st inp inp' : List (BitVec 8)) (q : Nat)
    (h : ∀ i, i < q → inp.getD i 0 = inp'.getD i 0) :
    xorBytesUpTo st inp q = xorBytesUpTo st inp' q := by
  induction q generalizing st with
  | zero => rfl
  | succ q ih =>
    simp only [xorBytesUpTo]
    have hq : inp.getD q 0 = inp'.getD q 0 := h q (Nat.lt_succ_self _)
    have hih := ih st (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self _)))
    simp only [hih, hq]

private theorem getD_take_prefix (msg : List (BitVec 8)) (m i : Nat) (hi : i < m) :
    (msg.take m).getD i 0 = msg.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases him : i < msg.length
  · have : i < (msg.take m).length := by
      rw [List.length_take, Nat.min_def]; split <;> omega
    rw [List.getElem?_eq_getElem him, List.getElem?_eq_getElem this,
      List.getElem_take]
  · have : ¬ i < (msg.take m).length := by
      rw [List.length_take, Nat.min_def]; split <;> omega
    rw [List.getElem?_eq_none (Nat.ge_of_not_lt him),
      List.getElem?_eq_none (Nat.ge_of_not_lt this)]

/-- Short-domain recovery: with no completed rate block the sponge is plain
    `xorBytesUpTo` from the zero state (the SegLoop invariant). -/
theorem kssAbsorbed_of_lt_rate (msg : List (BitVec 8)) (m : Nat)
    (hm : m < keccakAbsorbStep) :
    kssAbsorbed msg m = keccakRemAbsorbed keccakZeroStateBytes msg m := by
  have hdiv : m / keccakAbsorbStep = 0 := Nat.div_eq_of_lt hm
  have hmod : m % keccakAbsorbStep = m := Nat.mod_eq_of_lt hm
  simp only [kssAbsorbed, hdiv, hmod, keccakAbsorbedPrefix]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; rfl
  · simp only [keccakRemAbsorbed, Nat.ne_of_gt hpos, ↓reduceIte]
    exact xorBytesUpTo_congr_prefix _ _ _ _ (fun i hi => getD_take_prefix msg m i hi)

/-- When `m ≤ 135` and we are past the rem=0 edge, RemAbsorbed is xorBytesUpTo. -/
theorem kssAbsorbed_short (msg : List (BitVec 8)) (m : Nat)
    (hm : m ≤ 135) (hpos : 0 < m) :
    kssAbsorbed msg m = xorBytesUpTo keccakZeroStateBytes msg m := by
  have hlt : m < keccakAbsorbStep := by
    simp only [keccakAbsorbStep]; omega
  rw [kssAbsorbed_of_lt_rate msg m hlt, keccakRemAbsorbed_pos _ _ _ hpos]

/-! ## Fill step (non-boundary) -/

theorem kssFill_succ_of_lt (m : Nat)
    (h : kssFill m + 1 < keccakAbsorbStep) :
    kssFill (m + 1) = kssFill m + 1 := by
  simp only [kssFill] at h ⊢
  have h1 : 1 % keccakAbsorbStep = 1 := Nat.mod_eq_of_lt (by decide)
  calc
    (m + 1) % keccakAbsorbStep
        = (m % keccakAbsorbStep + 1 % keccakAbsorbStep) % keccakAbsorbStep := by
          rw [Nat.add_mod]
    _ = (m % keccakAbsorbStep + 1) % keccakAbsorbStep := by rw [h1]
    _ = m % keccakAbsorbStep + 1 := Nat.mod_eq_of_lt h

/-- Rate-boundary fill reset: when `fill = 135`, the next byte completes the
    block and the machine sets `s4 := 0` after permute. -/
theorem kssFill_succ_of_rate (m : Nat) (h : kssFill m = keccakAbsorbStep - 1) :
    kssFill (m + 1) = 0 := by
  simp only [kssFill] at h ⊢
  have hrem : m % keccakAbsorbStep = 135 := by
    simpa [keccakAbsorbStep] using h
  have : m + 1 = keccakAbsorbStep * (m / keccakAbsorbStep + 1) := by
    have hm := (Nat.div_add_mod m keccakAbsorbStep).symm
    simp only [keccakAbsorbStep] at hrem hm ⊢
    omega
  rw [this, Nat.mul_mod_right]

/-! ## Byte-step absorb (non-boundary: `fill + 1 < 136`) -/

private theorem xorBytesUpTo_succ_eq (st inp : List (BitVec 8)) (q : Nat) :
    xorBytesUpTo st inp (q + 1) =
      setBytes (xorBytesUpTo st inp q) q
        [(inp.getD q 0) ^^^ ((xorBytesUpTo st inp q).getD q 0)] := rfl

private theorem getD_drop (msg : List (BitVec 8)) (off i : Nat) :
    (msg.drop off).getD i 0 = msg.getD (off + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem take_getD_eq_getD (xs : List (BitVec 8)) (n i : Nat) (hi : i < n) :
    (xs.take n).getD i 0 = xs.getD i 0 :=
  getD_take_prefix xs n i hi

private theorem kss_div_succ_of_lt_fill (m : Nat)
    (h : m % keccakAbsorbStep + 1 < keccakAbsorbStep) :
    (m + 1) / keccakAbsorbStep = m / keccakAbsorbStep := by
  rw [show m + 1 =
        keccakAbsorbStep * (m / keccakAbsorbStep) + (m % keccakAbsorbStep + 1) from by
      have := (Nat.div_add_mod m keccakAbsorbStep).symm; omega]
  rw [Nat.mul_add_div (by decide : 0 < keccakAbsorbStep)]
  simp only [Nat.div_eq_of_lt h, Nat.add_zero]

/-- One-byte sponge step when the rate block does not complete. -/
theorem kssAbsorbed_succ_of_lt_fill (msg : List (BitVec 8)) (m : Nat)
    (h : kssFill m + 1 < keccakAbsorbStep) :
    kssAbsorbed msg (m + 1) =
      let st := kssAbsorbed msg m
      let fill := kssFill m
      setBytes st fill [(msg.getD m 0) ^^^ (st.getD fill 0)] := by
  have hrem_lt : m % keccakAbsorbStep + 1 < keccakAbsorbStep := by
    simpa [kssFill] using h
  have hN' := kss_div_succ_of_lt_fill m hrem_lt
  have hrem' : (m + 1) % keccakAbsorbStep = m % keccakAbsorbStep + 1 :=
    kssFill_succ_of_lt m h
  set N := m / keccakAbsorbStep
  set r := m % keccakAbsorbStep
  set stN := keccakAbsorbedPrefix msg N
  set tail := msg.drop (keccakAbsorbStep * N)
  have hpos' : 0 < r + 1 := Nat.succ_pos _
  -- Unfold both sides
  change
      keccakRemAbsorbed (keccakAbsorbedPrefix msg ((m + 1) / keccakAbsorbStep))
          ((msg.drop (keccakAbsorbStep * ((m + 1) / keccakAbsorbStep))).take
            ((m + 1) % keccakAbsorbStep))
          ((m + 1) % keccakAbsorbStep) =
        setBytes (kssAbsorbed msg m) (kssFill m)
          [(msg.getD m 0) ^^^ ((kssAbsorbed msg m).getD (kssFill m) 0)]
  simp only [hN', hrem', kssFill, kssAbsorbed,
    show N = m / keccakAbsorbStep from rfl,
    show r = m % keccakAbsorbStep from rfl]
  -- Goal uses stN / tail via N,r
  change
      keccakRemAbsorbed stN (tail.take (r + 1)) (r + 1) =
        setBytes (keccakRemAbsorbed stN (tail.take r) r) r
          [(msg.getD m 0) ^^^
            ((keccakRemAbsorbed stN (tail.take r) r).getD r 0)]
  simp only [keccakRemAbsorbed, Nat.ne_of_gt hpos', ↓reduceIte]
  rw [xorBytesUpTo_succ_eq]
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- rem = 0
    rw [hr0]
    simp only [↓reduceIte, xorBytesUpTo]
    have hbyte0 : (tail.take 1).getD 0 0 = msg.getD m 0 := by
      have htake : (tail.take 1).getD 0 0 = tail.getD 0 0 := by
        cases tail <;> rfl
      rw [htake, getD_drop]
      have hm0 : keccakAbsorbStep * N = m := by
        have hdiv := Nat.div_add_mod m keccakAbsorbStep
        simp only [N, r] at hdiv hr0 ⊢
        omega
      simp only [hm0, Nat.add_zero]
    simp only [hbyte0]
  · have hrne : r ≠ 0 := Nat.pos_iff_ne_zero.mp hrpos
    simp only [hrne, ↓reduceIte]
    have hcong :
        xorBytesUpTo stN (tail.take (r + 1)) r =
          xorBytesUpTo stN (tail.take r) r :=
      xorBytesUpTo_congr_prefix stN (tail.take (r + 1)) (tail.take r) r
        (fun i hi => by
          rw [take_getD_eq_getD _ (r + 1) i (Nat.lt_trans hi (Nat.lt_succ_self _)),
            take_getD_eq_getD _ r i hi])
    have hbyte : (tail.take (r + 1)).getD r 0 = msg.getD m 0 := by
      rw [take_getD_eq_getD _ (r + 1) r (Nat.lt_succ_self _), getD_drop]
      have : keccakAbsorbStep * N + r = m := by
        simp only [N, r]; exact Nat.div_add_mod m keccakAbsorbStep
      simp only [this]
    simp only [hcong, hbyte]

/-! ## Rate-boundary absorb (`fill = 135` → completed block) -/

/-- After the byte that fills the rate block, `kssAbsorbed` is exactly the next
    `keccakAbsorbedPrefix` (rem = 0). -/
theorem kssAbsorbed_succ_of_rate (msg : List (BitVec 8)) (m : Nat)
    (h : kssFill m = keccakAbsorbStep - 1) :
    kssAbsorbed msg (m + 1) =
      keccakAbsorbedPrefix msg (m / keccakAbsorbStep + 1) := by
  have hrem : m % keccakAbsorbStep = 135 := by
    simpa [kssFill, keccakAbsorbStep] using h
  have hdiv : (m + 1) / keccakAbsorbStep = m / keccakAbsorbStep + 1 := by
    have : m + 1 = keccakAbsorbStep * (m / keccakAbsorbStep + 1) := by
      have hm := (Nat.div_add_mod m keccakAbsorbStep).symm
      simp only [keccakAbsorbStep] at hrem hm ⊢
      omega
    rw [this, Nat.mul_div_right _ (by decide : 0 < keccakAbsorbStep)]
  have hmod : (m + 1) % keccakAbsorbStep = 0 := kssFill_succ_of_rate m h
  simp only [kssAbsorbed, hdiv, hmod, keccakRemAbsorbed_zero, List.take_zero]

/-- Pre-permute state after the last byte of a rate block: one `xorBytesUpTo`
    step past the `fill = 135` sponge. -/
theorem kss_rate_prePermute (msg : List (BitVec 8)) (m : Nat)
    (h : kssFill m = keccakAbsorbStep - 1) :
    let st := kssAbsorbed msg m
    let st' := setBytes st (keccakAbsorbStep - 1)
      [(msg.getD m 0) ^^^ (st.getD (keccakAbsorbStep - 1) 0)]
    let N := m / keccakAbsorbStep
    let block := (msg.drop (keccakAbsorbStep * N)).take keccakAbsorbStep
    st' = xorBytesUpTo (keccakAbsorbedPrefix msg N) block keccakAbsorbStep := by
  have hrem : m % keccakAbsorbStep = 135 := by
    simpa [kssFill, keccakAbsorbStep] using h
  set N := m / keccakAbsorbStep
  set stN := keccakAbsorbedPrefix msg N
  set tail := msg.drop (keccakAbsorbStep * N)
  set block := tail.take keccakAbsorbStep
  have hpos : 0 < (135 : Nat) := by decide
  -- kssAbsorbed msg m = xorBytesUpTo stN (tail.take 135) 135
  have habs : kssAbsorbed msg m = xorBytesUpTo stN (tail.take 135) 135 := by
    simp only [kssAbsorbed, keccakRemAbsorbed, hrem, Nat.ne_of_gt hpos,
      ↓reduceIte, keccakAbsorbStep]
    rfl
  change
      setBytes (kssAbsorbed msg m) 135
          [(msg.getD m 0) ^^^ ((kssAbsorbed msg m).getD 135 0)] =
        xorBytesUpTo stN block 136
  rw [habs]
  have hrhs :
      xorBytesUpTo stN block 136 =
        setBytes (xorBytesUpTo stN (tail.take 136) 135) 135
          [((tail.take 136).getD 135 0) ^^^
            ((xorBytesUpTo stN (tail.take 136) 135).getD 135 0)] := by
    simp only [block, keccakAbsorbStep]
    exact xorBytesUpTo_succ_eq stN (tail.take 136) 135
  have hcong :
      xorBytesUpTo stN (tail.take 136) 135 =
        xorBytesUpTo stN (tail.take 135) 135 :=
    xorBytesUpTo_congr_prefix stN (tail.take 136) (tail.take 135) 135
      (fun i hi => by
        have : i < 136 := by omega
        rw [take_getD_eq_getD _ 136 i this, take_getD_eq_getD _ 135 i hi])
  have hbyte : (tail.take 136).getD 135 0 = msg.getD m 0 := by
    rw [take_getD_eq_getD _ 136 135 (by decide), getD_drop]
    have : keccakAbsorbStep * N + 135 = m := by
      have := Nat.div_add_mod m keccakAbsorbStep
      simp only [N, keccakAbsorbStep, hrem] at this ⊢
      omega
    simp only [keccakAbsorbStep, this]
  rw [hrhs, hcong, hbyte]

/-- Rate-boundary CSRS: byte-XOR the completing byte, then `keccakBytes`, recovers
    `kssAbsorbed (m+1)` (= next `keccakAbsorbedPrefix`).

    Requires the completed block to be present in `msg` (`m + 1 ≤ msg.length`) so
    the rate window has length 136 — the machine only reaches this path after
    absorbing 136 real bytes. -/
theorem kssAbsorbed_succ_of_rate_csrs (msg : List (BitVec 8)) (m : Nat)
    (h : kssFill m = keccakAbsorbStep - 1)
    (hlen : m + 1 ≤ msg.length) :
    kssAbsorbed msg (m + 1) =
      let st := kssAbsorbed msg m
      let st' := setBytes st (keccakAbsorbStep - 1)
        [(msg.getD m 0) ^^^ (st.getD (keccakAbsorbStep - 1) 0)]
      setBytes st' 0 (keccakBytes st' 0) := by
  have hrem : m % keccakAbsorbStep = 135 := by
    simpa [kssFill, keccakAbsorbStep] using h
  set N := m / keccakAbsorbStep
  set stN := keccakAbsorbedPrefix msg N
  set tail := msg.drop (keccakAbsorbStep * N)
  set block := tail.take keccakAbsorbStep
  have hstN_len : stN.length = 200 := keccakAbsorbedPrefix_length msg N
  have hblk : block.length = 136 := by
    simp only [block, tail, List.length_take, List.length_drop, keccakAbsorbStep]
    have : 136 * N + 136 ≤ msg.length := by
      have hm := (Nat.div_add_mod m keccakAbsorbStep).symm
      simp only [N, keccakAbsorbStep, hrem] at hm hlen ⊢
      omega
    omega
  have hpre : setBytes (kssAbsorbed msg m) 135
        [(msg.getD m 0) ^^^ ((kssAbsorbed msg m).getD 135 0)] =
      xorBytesUpTo stN block 136 := by
    simpa [keccakAbsorbStep, stN, block, tail, N] using kss_rate_prePermute msg m h
  have hsucc : kssAbsorbed msg (m + 1) =
      keccakAbsorbedPrefix msg (m / keccakAbsorbStep + 1) :=
    kssAbsorbed_succ_of_rate msg m h
  have hprefix : keccakAbsorbedPrefix msg (m / keccakAbsorbStep + 1) =
      keccakPermuteAbsorbed stN block := by
    simp only [stN, block, tail, N, keccakAbsorbedPrefix_succ]
  have hperm : keccakPermuteAbsorbed stN block =
      setBytes (xorBytesUpTo stN block 136) 0
        (keccakBytes (xorBytesUpTo stN block 136) 0) :=
    keccakPermuteAbsorbed_eq_byteXor stN block hstN_len hblk
  calc
    kssAbsorbed msg (m + 1)
        = keccakAbsorbedPrefix msg (m / keccakAbsorbStep + 1) := hsucc
    _ = keccakPermuteAbsorbed stN block := hprefix
    _ = setBytes (xorBytesUpTo stN block 136) 0
          (keccakBytes (xorBytesUpTo stN block 136) 0) := hperm
    _ = setBytes
          (setBytes (kssAbsorbed msg m) 135
            [(msg.getD m 0) ^^^ ((kssAbsorbed msg m).getD 135 0)])
          0
          (keccakBytes
            (setBytes (kssAbsorbed msg m) 135
              [(msg.getD m 0) ^^^ ((kssAbsorbed msg m).getD 135 0)])
            0) := by
        rw [← hpre]

/-! ## Digest bridge at arbitrary length -/

/-- `kssFinalState` is exactly the sponge image inside `keccakBodyDigest`. -/
theorem keccakBodyDigest_eq_kssFinalState (input : List (BitVec 8)) (N rem : Nat) :
    keccakBodyDigest input N rem =
      keccakDigestCopy (kssFinalState (keccakBodyPrePad input N rem) rem) := by
  simp only [keccakBodyDigest, kssFinalState]

/-- Segments absorb + fill plug into the body-digest construction. -/
theorem kss_digestCopy_final_eq_bodyDigest (msg : List (BitVec 8)) :
    keccakDigestCopy
        (kssFinalState (kssAbsorbed msg msg.length) (kssFill msg.length))
      = keccakBodyDigest msg (msg.length / keccakAbsorbStep)
          (msg.length % keccakAbsorbStep) := by
  rw [keccakBodyDigest_eq_kssFinalState, kssAbsorbed_eq_bodyPrePad]
  rfl

/-- General SpecRef reduction via `#12104` at nonzero `N`. -/
theorem kssDigest_eq_specref_any (msg : List (BitVec 8)) :
    keccakDigestCopy
        (kssFinalState (kssAbsorbed msg msg.length) (kssFill msg.length))
      = Stateless.SpecRef.keccak256 msg :=
  (kss_digestCopy_final_eq_bodyDigest msg).trans <|
    keccakBodyDigest_eq_specref msg
      (msg.length / keccakAbsorbStep) (msg.length % keccakAbsorbStep)
      (Nat.div_add_mod msg.length keccakAbsorbStep).symm
      (Nat.mod_lt _ (by decide))

/-- Short-domain digest recovers from the general lemma. -/
theorem kssDigest_eq_specref_of_short (msg : List (BitVec 8))
    (hshort : msg.length ≤ 135) :
    keccakDigestCopy
        (kssFinalState (xorBytesUpTo keccakZeroStateBytes msg msg.length)
          msg.length)
      = Stateless.SpecRef.keccak256 msg := by
  have hfill : kssFill msg.length = msg.length :=
    kssFill_of_le_rate _ (by simp only [keccakAbsorbStep]; omega)
  have habs : kssAbsorbed msg msg.length =
      xorBytesUpTo keccakZeroStateBytes msg msg.length := by
    rcases Nat.eq_zero_or_pos msg.length with h0 | hpos
    · rw [h0, kssAbsorbed_zero]
      rfl
    · exact kssAbsorbed_short msg msg.length hshort hpos
  have H := kssDigest_eq_specref_any msg
  rw [habs, hfill] at H
  exact H

end EvmAsm.Codegen.Proofs
