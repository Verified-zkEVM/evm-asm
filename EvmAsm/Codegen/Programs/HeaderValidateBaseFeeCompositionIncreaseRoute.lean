/-
  Increase-route composition toward the Route-B K73 contract (#12346 item 2b).

  The increasing arm ships a fully-composed entry-to-return theorem
  (`k73_increase_entry_status_div_zero_to_return_general_spec_within`), but its
  merged final post (`k73IncreaseStatusFinalPost`) drops the runtime is-zero
  fact that decides which clamp path the machine took.  The Route-B written
  image differs between the two paths (`parentFee + raw` versus
  `parentFee + 1`), so the adapter assembles from seams instead, threading the
  fact through:

    entry            (premise-free)                  K73 .. K73 + 84
    mul call/status  (deployed mul callee)           K73 + 84 .. K73 + 92
    div pair         (premise-free, htargetPos)      K73 + 92 .. K73 + 124
    is_zero call     (strengthened: result valued)   K73 + 124 .. K73 + 136
    zero branch      (facts: raw = 0 / raw <> 0)     K73 + 136 .. K73 + 172
    add chain + tails                                K73 + 172 .. raIn

  The spec clamps on increase (`baseFeeIncreaseDelta = max (raw) 1`), matching
  the machine's `is_zero`/`from_u64(1)` replacement, so the written image
  equality is true with no divergence; the only data guard is `hMulFit` (mul
  no-overflow), exactly as in the decreasing arm.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeRoutes
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeBranches
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Proofs.U256IsZeroSpec
import EvmAsm.Codegen.Programs.U256MulU64Be.Arith
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseRoute
import EvmAsm.Crypto.BeBytesArith
import EvmAsm.Rv64.Tactics.XPermCert

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec

/-! ## Window-value zero test -/

/-- Big-endian byte-list value is zero exactly when every byte is zero. -/
private theorem k73_beBytes_eq_zero_iff (l : List (BitVec 8)) :
    EvmAsm.Crypto.beBytesToNat l = 0 ↔ ∀ b ∈ l, (b : BitVec 8) = 0 := by
  induction l with
  | nil => simp [EvmAsm.Crypto.beBytesToNat]
  | cons b bs ih =>
    rw [EvmAsm.Crypto.beBytesToNat_cons]
    constructor
    · intro h
      have hpow : 0 < 256 ^ bs.length := by positivity
      have hmul : b.toNat * 256 ^ bs.length = 0 := by omega
      have hb0 : b.toNat = 0 := by
        rcases Nat.mul_eq_zero.mp hmul with hz | hp
        · exact hz
        · exact absurd hp (by omega)
      have hb : (b : BitVec 8) = 0 := BitVec.eq_of_toNat_eq (by simp [hb0])
      have hrz : EvmAsm.Crypto.beBytesToNat bs = 0 := by omega
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hbs
      · exact hb
      · exact (ih.mp hrz) c hbs
    · intro h
      have hb0 : (b : BitVec 8) = 0 := h b (by simp)
      have hrz : EvmAsm.Crypto.beBytesToNat bs = 0 :=
        ih.mpr fun c hc => h c (List.mem_cons_of_mem _ hc)
      have ht : b.toNat = 0 := by rw [hb0]; rfl
      rw [ht, hrz]
      simp

/-- An 8-byte chunk packs to zero exactly when all its bytes are zero. -/
private theorem k73_packBytes_eq_zero_iff {c : List (BitVec 8)} (hc : c.length = 8) :
    packBytes c = 0 ↔ ∀ b ∈ c, (b : BitVec 8) = 0 := by
  constructor
  · intro h b hb
    obtain ⟨j, hj, hbj⟩ := List.mem_iff_getElem.mp hb
    have hpack : extractByte (packBytes c) j = b := by rw [extractByte_packBytes c j (by omega) (by simp [hc]; omega)]; exact hbj
    have hz : ∀ k : Nat, extractByte (0 : Word) k = 0 := by
      intro k
      simp [EvmAsm.Rv64.extractByte]
    rw [h] at hpack
    rw [hz] at hpack
    exact hpack.symm
  · intro h
    have hrep : c = List.replicate 8 0 := by
      apply List.ext_get
      · simp [hc]
      · intro n hn1 hn2
        have hbz : c[n] = 0 := h (c[n]) (List.getElem_mem (by simpa [hc] using hn1))
        show c[n] = (List.replicate 8 0)[n]
        rw [hbz, List.getElem_replicate (by simpa using hn2)]
    rw [hrep]
    rfl

/-- A length-32 window tests zero exactly when all four of its
`bytesRegion`-spelled dwords are zero. -/
theorem k73_incr_window_zero_iff (q2 : List (BitVec 8)) (hlen : q2.length = 32) :
    EvmAsm.Crypto.beBytesToNat q2 = 0 ↔
      packBytes (q2.take 8) = 0 ∧ packBytes ((q2.drop 8).take 8) = 0 ∧
        packBytes ((q2.drop 16).take 8) = 0 ∧
        packBytes ((q2.drop 24).take 8) = 0 := by
  have hlen1 : (q2.take 8).length = 8 := by
    rw [List.length_take]; simp only [hlen]; omega
  have hlen2 : ((q2.drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; simp only [hlen]; omega
  have hlen3 : ((q2.drop 16).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; simp only [hlen]; omega
  have hlen4 : ((q2.drop 24).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; simp only [hlen]; omega
  constructor
  · intro h
    have hall := (k73_beBytes_eq_zero_iff q2).mp h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (k73_packBytes_eq_zero_iff hlen1).mpr
        fun b hb => hall b (List.mem_of_mem_take hb)
    · exact (k73_packBytes_eq_zero_iff hlen2).mpr
        fun b hb => hall b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
    · exact (k73_packBytes_eq_zero_iff hlen3).mpr
        fun b hb => hall b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
    · exact (k73_packBytes_eq_zero_iff hlen4).mpr
        fun b hb => hall b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  · intro h
    obtain ⟨h0, h1, h2, h3⟩ := h
    have z0 := (k73_packBytes_eq_zero_iff hlen1).mp h0
    have z1 := (k73_packBytes_eq_zero_iff hlen2).mp h1
    have z2 := (k73_packBytes_eq_zero_iff hlen3).mp h2
    have z3 := (k73_packBytes_eq_zero_iff hlen4).mp h3
    refine (k73_beBytes_eq_zero_iff q2).mpr ?_
    intro b hb
    obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
    rcases Nat.lt_or_ge j 8 with hj8 | hj8
    · refine z0 b (List.mem_iff_getElem.mpr ⟨j, by omega, ?_⟩)
      simp only [List.getElem_take]
      exact hjb
    rcases Nat.lt_or_ge j 16 with h16 | h16
    · refine z1 b (List.mem_iff_getElem.mpr ⟨j - 8, by omega, ?_⟩)
      rw [List.getElem_take, ← hjb, List.getElem_drop]
      congr 1
      omega
    rcases Nat.lt_or_ge j 24 with h24 | h24
    · refine z2 b (List.mem_iff_getElem.mpr ⟨j - 16, by omega, ?_⟩)
      rw [List.getElem_take, ← hjb, List.getElem_drop]
      congr 1
      omega
    · refine z3 b (List.mem_iff_getElem.mpr ⟨j - 24, by omega, ?_⟩)
      rw [List.getElem_take, ← hjb, List.getElem_drop]
      congr 1
      omega

/-- Pure-Nat core of the increase written-image equality: the machine adds
either the raw delta (taken when it is nonzero) or the clamped 1 (taken when
it is zero), and the spec adds `max raw 1`. -/
theorem k73_incr_w_core (fee raw addend : Nat)
    (h : (raw = 0 ∧ addend = 1) ∨ (addend = raw ∧ 0 < raw)) :
    (fee + addend) % 2 ^ 256 = (fee + Nat.max raw 1) % 2 ^ 256 := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · subst h0
    subst h1
    simp [Nat.max]
  · subst h0
    exact (congrArg (fun n => (fee + n) % 2 ^ 256) (Nat.max_eq_left h1)).symm

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute
