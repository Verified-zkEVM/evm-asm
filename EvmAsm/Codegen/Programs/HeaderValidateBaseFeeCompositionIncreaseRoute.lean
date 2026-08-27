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
import EvmAsm.Codegen.Programs.U256AddBeBInPlaceSAsm
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionDecreaseRoute
import EvmAsm.Crypto.BeBytesArith
import EvmAsm.Rv64.Tactics.XPermCert

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.U256DivU64BeSAsm EvmAsm.Codegen.Proofs

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

/-! ### Strengthened is_zero call seam

`k73_increase_is_zero_call_spec_within` (HeaderBaseFeeWholeSpec) flattens the
callee's result pin to `regOwn .x10`; the zero-branch downstream therefore
cannot learn the runtime outcome it tests.  This variant keeps the callee's
valued `x10` pin (same 11-step window, same atoms otherwise) so the
strengthened zero branch can emit the semantic zero facts as pure conjuncts.
Proof: clone of the source seam minus the final pin-to-ownership lift. -/
theorem k73_increase_is_zero_call_valued_spec_within
    (ptr oldRa : Word) (w0 w1 w2 w3 : Word) (F : Assertion)
    (hF : F.pcFree) :
    ∀ old10, cpsTripleWithin 11 (K73 + 128) (K73 + 136) wholeCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
          (1 : Word) else 0)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) := by
  intro old10
  let tail : List Reg :=
    [.x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]
  have htail : ∀ vf : Reg → Word,
      regAtomsOf vf u256DivU64BeScratch =
        (((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          regAtomsOf vf tail) := by
    intro vf
    simp only [u256DivU64BeScratch, tail, regAtomsOf_cons, regAtomsOf_nil]
  have hmvAny : cpsTripleWithin 1 (K73 + 128) (K73 + 132) wholeCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) := by
    have hmv := mv_spec_gen_within .x10 .x9 ptr old10 (K73 + 128) (by decide)
    have hmvC := cpsTripleWithin_extend_code
      (k73_whole_mem 32 _ (K73 + 128) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hmv
    have hR : (((.x1 : Reg) ↦ᵣ oldRa) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F).pcFree := by
      pcf
      exact hF
    have hmvF := cpsTripleWithin_frameR _ hR hmvC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hmvF
  have htarget :
      (K73 + 132) + signExtend21
        (jalOff GuestAddrs.u256_is_zero
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 132)) =
        (GuestAddrs.u256_is_zero : Word) := by
    change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 132 + _ = BitVec.ofNat 64 GuestAddrs.u256_is_zero
    exact jalOff_correct_add GuestAddrs.u256_is_zero
      GuestAddrs.eip1559_calc_base_fee_per_gas 132
      (by decide) (by decide) (by decide) (by decide)
  have hmem : ∀ a i, CodeReq.singleton (K73 + 132)
      (.JAL .x1 (jalOff GuestAddrs.u256_is_zero
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 132))) a = some i →
      wholeCode a = some i := by
    intro a i hi
    exact k73_whole_mem 33 _ (K73 + 132) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi
  have hcallAny : ∀ vf : Reg → Word,
      cpsTripleWithin 10 (K73 + 132) (K73 + 136) wholeCode
      (((((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regAtomsOf vf u256DivU64BeScratch))
      (((((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
          (1 : Word) else 0)) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regOwns u256DivU64BeScratch)) := by
    intro vf
    have hzero := u256IsZeroFlat_spec_domain ptr (K73 + 136)
      (vf .x5) (vf .x6) (vf .x7) (vf .x28) w0 w1 w2 w3
    have hzeroC := cpsTripleWithin_extend_code isZero_whole_mono hzero
    have hP0 : (((.x10 : Reg) ↦ᵣ ptr) **
        ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
        ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3))).pcFree := by
      pcf
    have hcallee0 : cpsTripleWithin 9 (GuestAddrs.u256_is_zero : Word)
        (K73 + 136) wholeCode
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x10 : Reg) ↦ᵣ ptr) **
          ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)))
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
          ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
            (1 : Word) else 0)) **
          ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
          ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
          ((.x28 : Reg) ↦ᵣ w3) **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3))) := by
      exact cpsTripleWithin_weaken
        (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) hzeroC
    have hcall0 := callWithin_spec
      (cr := wholeCode)
      (P := ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
        ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)))
      (Q := ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
          (1 : Word) else 0)) **
        ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
        ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
        ((.x28 : Reg) ↦ᵣ w3) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)))
      (K73 + 132) (GuestAddrs.u256_is_zero : Word) oldRa
      (jalOff GuestAddrs.u256_is_zero
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 132)) 9 htarget hmem hP0 hcallee0
    have hcallF := cpsTripleWithin_frameR
      (regAtomsOf vf tail ** F) (by dsimp [tail]; pcf; exact hF) hcall0
    have hcall : cpsTripleWithin 10 (K73 + 132) (K73 + 136) wholeCode
        (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
          ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          regAtomsOf vf tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
          ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
            (1 : Word) else 0)) **
          ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
          ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
          ((.x28 : Reg) ↦ᵣ w3) ** regAtomsOf vf tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) := by
      simpa only [show 1 + 9 = 10 by decide, sepConj_assoc', sepConj_comm',
        sepConj_left_comm',
        show (K73 + 132) + 4 = K73 + 136 by bv_omega] using hcallF
    exact cpsTripleWithin_weaken
      (P' := (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regAtomsOf vf u256DivU64BeScratch)
      (Q' := (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
          (1 : Word) else 0)) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regOwns u256DivU64BeScratch)
      (fun _ hp => by
        rw [htail vf] at hp
        xperm_hyp hp)
      (fun s hq => by
        have hq0 :
            (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
              ((.x10 : Reg) ↦ᵣ
                (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
                  (1 : Word) else 0)) **
              ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
              ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
              ((.x28 : Reg) ↦ᵣ w3) ** regAtomsOf vf tail **
              ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
              ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) s := by
          xperm_hyp hq
        have hownChain : ∀ v10 v5 v6 v7 v28 : Word, ∀ s,
            (((.x10 : Reg) ↦ᵣ v10) ** ((.x5 : Reg) ↦ᵣ v5) **
              ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
              ((.x28 : Reg) ↦ᵣ v28) ** regAtomsOf vf tail **
              ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
                ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) s →
            (((.x10 : Reg) ↦ᵣ v10) ** regOwn .x5 ** regOwn .x6 **
              regOwn .x7 ** regOwn .x28 ** regOwns tail **
              ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
                ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) s := by
          intro v10 v5 v6 v7 v28 s hs
          exact sepConj_mono (fun _ h => h)
            (sepConj_mono (regIs_implies_regOwn .x5)
              (sepConj_mono (regIs_implies_regOwn .x6)
                (sepConj_mono (regIs_implies_regOwn .x7)
                  (sepConj_mono (regIs_implies_regOwn .x28)
                    (sepConj_mono (fun s h => regAtomsOf_to_regOwns vf tail s h)
                      (fun _ h => h)))))) s hs
        have hq1 := sepConj_mono_right
          (hownChain (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
            (1 : Word) else 0) (w0 ||| w1 ||| w2 ||| w3) w1 w2 w3) _ hq0
        simp only [tail, u256DivU64BeScratch, regOwns] at hq1 ⊢
        xperm_hyp hq1) hcall
  have hcallOwn := cpsTripleWithin_peel_regOwns u256DivU64BeScratch (by decide)
    (P := ((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
    (Q := ((((.x1 : Reg) ↦ᵣ (K73 + 136)) **
      ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
        (1 : Word) else 0)) **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
      regOwns u256DivU64BeScratch)) hcallAny
  have hcallFramed := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr)) (by pcf) hcallOwn
  have hcallFramed' := cpsTripleWithin_weaken
    (P' := (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F))
    (Q' := (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
        (1 : Word) else 0)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
        ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F))
    (fun _ hp => by
      simp only [u256DivU64BeScratch, regOwns] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [u256DivU64BeScratch, regOwns] at hq ⊢
      xperm_hyp hq) hcallFramed
  have hseq := cpsTripleWithin_seq_same_cr hmvAny hcallFramed'
  exact hseq

/-! ### Zero-test branch with semantic facts

`k73_increase_zero_branch_spec_within` discards the `BEQZ` outcome facts
(`old10 = 0` / `old10 ≠ 0`) that `beq_spec_gen_within` already extracts, so
downstream W-casts cannot learn whether the accumulator was replaced.  We keep
them: a branch variant whose exits carry the outcome as pure conjuncts, and
two deterministic case theorems (static `beBytesToNat q2` zero / nonzero)
each concluding a single-exit triple feeding the corresponding final arm. -/

private theorem k73_incr_vacuous_triple {P Q : Assertion} {a b : Word}
    {n : Nat} (hP : ∀ s, P s → False) :
    cpsTripleWithin n a b wholeCode P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨h, hcompat, h1, h2, hd, hu, hpl, hpr⟩ := hPR
  exact (hP _ hpl).elim

private theorem k73_incr_zero_branch_facts_spec_within
    (ptr : Word) (q2 : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    ∀ old10 : Word, cpsBranchWithin 1 (K73 + 136) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 172)
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜old10 = (0 : Word)⌝)
      (K73 + 140)
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ old10)) **
        ⌜old10 ≠ (0 : Word)⌝) := by
  intro old10
  let Base : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F
  let Rest : Assertion := ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Base
  have hBase : Base.pcFree := by
    dsimp [Base]
    pcf
    exact hF
  have hbeq := beq_spec_gen_within .x10 .x0 (36 : BitVec 13)
    old10 (0 : Word) (K73 + 136)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 34 _ (K73 + 136) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  have hbeqF := cpsBranchWithin_frameR Base hBase hbeqC
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun s hq => by
      have hq' :
          (((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
              Base) ** ⌜old10 = (0 : Word)⌝) s := by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq
      obtain ⟨hq, hzero⟩ := (sepConj_pure_right _).1 hq'
      rw [hzero] at hq
      dsimp only [Rest, Base] at hq
      have hq2 :
          ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
            ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
            ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
            bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word)))) s := by
        xperm_hyp hq
      exact (sepConj_pure_right _).2 ⟨hq2, hzero⟩)
    (fun s hq => by
      have hq' :
          (((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
              Base) ** ⌜old10 ≠ (0 : Word)⌝) s := by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq
      obtain ⟨hq, hne⟩ := (sepConj_pure_right _).1 hq'
      dsimp only [Rest, Base] at hq
      have hq2 :
          ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
            ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
            ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
            bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ old10))) s := by
        xperm_hyp hq
      exact (sepConj_pure_right _).2 ⟨hq2, hne⟩) hbeqF

/-- Nonzero case: the accumulator window holds a nonzero value, the
`is_zero` result is `0`, and the machine keeps the accumulator (BEQZ taken). -/
theorem k73_incr_zero_keep_spec_within
    (ptr : Word) (q2 : List (BitVec 8)) (F : Assertion)
    (_hrw : RwRegion.wf ⟨ptr, 32⟩) (hlen : q2.length = 32)
    (hF : F.pcFree) (hpNZ : EvmAsm.Crypto.beBytesToNat q2 ≠ 0) :
    cpsTripleWithin 1 (K73 + 136) (K73 + 172) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ (if packBytes ((q2.drop 0).take 8) = 0 ∧
            packBytes ((q2.drop 8).take 8) = 0 ∧
            packBytes ((q2.drop 16).take 8) = 0 ∧
            packBytes ((q2.drop 24).take 8) = 0 then (1 : Word) else 0)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F) := by
  have hnotAll : ¬(packBytes ((q2.drop 0).take 8) = 0 ∧
      packBytes ((q2.drop 8).take 8) = 0 ∧
      packBytes ((q2.drop 16).take 8) = 0 ∧
      packBytes ((q2.drop 24).take 8) = 0) := by
    intro h
    have hlemma : packBytes (List.take 8 q2) = 0 ∧
        packBytes (List.take 8 (List.drop 8 q2)) = 0 ∧
        packBytes (List.take 8 (List.drop 16 q2)) = 0 ∧
        packBytes (List.take 8 (List.drop 24 q2)) = 0 := by
      simpa only [List.drop_zero] using h
    exact hpNZ ((k73_incr_window_zero_iff q2 hlen).mpr hlemma)
  have hval : (if packBytes ((q2.drop 0).take 8) = 0 ∧
      packBytes ((q2.drop 8).take 8) = 0 ∧
      packBytes ((q2.drop 16).take 8) = 0 ∧
      packBytes ((q2.drop 24).take 8) = 0 then (1 : Word) else 0)
      = (0 : Word) := if_neg hnotAll
  have hbr := k73_incr_zero_branch_facts_spec_within ptr q2 F hF (0 : Word)
  have h_t0 : cpsTripleWithin 0 (K73 + 172) (K73 + 172) CodeReq.empty
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(0 : Word) = (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F) :=
    cpsTripleWithin_refl (fun _ h => by
      obtain ⟨hq, _⟩ := (sepConj_pure_right _).1 h
      xperm_hyp hq)
  have h_t : cpsTripleWithin 0 (K73 + 172) (K73 + 172) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(0 : Word) = (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F) :=
    cpsTripleWithin_extend_code (cr' := wholeCode)
      (fun a i hi => by simp [CodeReq.empty] at hi) h_t0

  have h_f : cpsTripleWithin 0 (K73 + 140) (K73 + 172) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(0 : Word) ≠ (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F) := by
    intro R hR s hcr hPR hpc
    obtain ⟨h, hcompat, h1, h2, hd, hu, hpl, hpr⟩ := hPR
    obtain ⟨_, hne⟩ := (sepConj_pure_right _).1 hpl
    exact absurd rfl hne
  have hmerge := cpsBranchWithin_merge_same_cr hbr h_t h_f
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hmerge
  · rw [hval] at hp
    xperm_hyp hp
  · exact hq

/-- Zero case: the accumulator window is all zero, the `is_zero` result is
`1`, and the machine replaces the accumulator with `u256_from_u64_be 1`
(BEQZ not taken, replacement route). -/
theorem k73_incr_zero_replace_spec_within
    (ptr : Word) (q2 : List (BitVec 8)) (F : Assertion)
    (hrw : RwRegion.wf ⟨ptr, 32⟩) (hlen : q2.length = 32)
    (hF : F.pcFree) (hpZ : EvmAsm.Crypto.beBytesToNat q2 = 0) :
    cpsTripleWithin
      (1 + (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1))
      (K73 + 136) (K73 + 172) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ (if packBytes ((q2.drop 0).take 8) = 0 ∧
            packBytes ((q2.drop 8).take 8) = 0 ∧
            packBytes ((q2.drop 16).take 8) = 0 ∧
            packBytes ((q2.drop 24).take 8) = 0 then (1 : Word) else 0)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** regOwns exposedRegs **
        bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) := by
  have hall : packBytes ((q2.drop 0).take 8) = 0 ∧
      packBytes ((q2.drop 8).take 8) = 0 ∧
      packBytes ((q2.drop 16).take 8) = 0 ∧
      packBytes ((q2.drop 24).take 8) = 0 := by
    have hlemma := (k73_incr_window_zero_iff q2 hlen).mp hpZ
    rw [show List.take 8 (List.drop 0 q2) = List.take 8 q2 from by simp]
    exact hlemma
  have hval : (if packBytes ((q2.drop 0).take 8) = 0 ∧
      packBytes ((q2.drop 8).take 8) = 0 ∧
      packBytes ((q2.drop 16).take 8) = 0 ∧
      packBytes ((q2.drop 24).take 8) = 0 then (1 : Word) else 0)
      = (1 : Word) := if_pos hall
  have hbr := k73_incr_zero_branch_facts_spec_within ptr q2 F hF (1 : Word)
  have hf0 := k73_increase_replace_route_spec_within ptr q2 F hrw hlen hF
  have h_t : cpsTripleWithin
      (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1)
      (K73 + 172) (K73 + 172) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(1 : Word) = (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** regOwns exposedRegs **
        bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) := by
    intro R hR s hcr hPR hpc
    obtain ⟨h, hcompat, h1, h2, hd, hu, hpl, hpr⟩ := hPR
    obtain ⟨_, hz⟩ := (sepConj_pure_right _).1 hpl
    exact absurd hz (by decide)
  have h_f : cpsTripleWithin
      (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1)
      (K73 + 140) (K73 + 172) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (1 : Word))) **
        ⌜(1 : Word) ≠ (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** regOwns exposedRegs **
        bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) := by
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hq => hq) hf0
    obtain ⟨hpair, _⟩ := (sepConj_pure_right _).1 hp
    have hmid : (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x9 : Reg) ↦ᵣ ptr) **
        (((.x11 : Reg) ↦ᵣ (8 : Word)) ** (((.x12 : Reg) ↦ᵣ ptr) **
        (regOwns u256DivU64BeScratch ** (bytesRegion ptr q2 ** F)))))))) s := by
      xperm_hyp hpair
    have hl3 : (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((regOwn .x10) ** (((.x9 : Reg) ↦ᵣ ptr) ** (((.x11 : Reg) ↦ᵣ (8 : Word)) **
        (((.x12 : Reg) ↦ᵣ ptr) ** (regOwns u256DivU64BeScratch **
        (bytesRegion ptr q2 ** F)))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id
        (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id
          (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift
            (r := Reg.x10) (v := (1 : Word)))) s hmid
    xperm_hyp hl3
  have hmerge := cpsBranchWithin_merge_same_cr hbr h_t h_f
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hmerge
  · rw [hval] at hp
    xperm_hyp hp
  · exact hq

/-! ## Increase-arm W-algebra -/

/-- Word-level delta unwrap on the increase arm: when the used gas sits
    strictly above the target, the register subtraction `gasUsed - target`
    does not wrap, so its numeric value is the plain difference. -/
private theorem k73_incr_word_delta_toNat (target gasUsed : Word)
    (hlt : target.toNat < gasUsed.toNat) :
    (gasUsed - target).toNat = gasUsed.toNat - target.toNat := by
  rw [BitVec.toNat_sub]
  have h1 : target.toNat < 2 ^ 64 := BitVec.isLt target
  have h2 : gasUsed.toNat < 2 ^ 64 := BitVec.isLt gasUsed
  omega

/-- Value of the written image on the increase arm: the spec clamps the
    delta at `1`, so the image encodes `(fee + max raw 1) mod 2^256`. -/
private theorem k73_incr_written_val
    {gasLimit gasUsed target : Word} {parentBytes : List (BitVec 8)}
    (htgtDef : target.toNat = gasLimit.toNat / 2)
    (hlt : target.toNat < gasUsed.toNat)
    (_hlenP : parentBytes.length = 32) :
    EvmAsm.Crypto.beBytesToNat (hvbfWrittenImage gasLimit gasUsed parentBytes)
      = (EvmAsm.Crypto.beBytesToNat parentBytes
          + Nat.max ((EvmAsm.Crypto.beBytesToNat parentBytes *
              (gasUsed.toNat - target.toNat)) / target.toNat / 8) 1)
        % 2 ^ 256 := by
  have hbB : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes
      = EvmAsm.Crypto.beBytesToNat parentBytes :=
    k73_bytesBEtoNat_eq_beBytesToNat parentBytes
  show EvmAsm.Crypto.beBytesToNat
      (EvmAsm.Stateless.SpecRef.natToBytesBE 32
        (EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide gasUsed.toNat
          (gasLimit.toNat / 2)
          (EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes))) = _
  have hswap : EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide gasUsed.toNat
      (gasLimit.toNat / 2)
      (EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes)
      = EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide gasUsed.toNat
        (gasLimit.toNat / 2)
        (EvmAsm.Crypto.beBytesToNat parentBytes) := by
    rw [hbB]
  have hneOuter : Not ((gasUsed.toNat == gasLimit.toNat / 2) = true) := by
    intro hc
    have hge := beq_iff_eq.mp hc
    omega
  have hgtInner : gasUsed.toNat > gasLimit.toNat / 2 := by
    omega
  rw [hswap, EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide,
    if_neg hneOuter, if_pos hgtInner, ← htgtDef,
    EvmAsm.Stateless.SpecRef.baseFeeIncreaseDelta_eq_reference]
  have hvv := k73_fixed_bytes_value 32
    (EvmAsm.Crypto.beBytesToNat parentBytes
      + Nat.max ((EvmAsm.Crypto.beBytesToNat parentBytes *
          (gasUsed.toNat - target.toNat)) / target.toNat / 8) 1)
  rw [hvv]
  rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]


/-- Machine output value on the increase KEEP arm: the window the add reads
    is the twice-divided accumulator, numerically `raw`, and `raw` is nonzero
    on this arm so the clamp `max raw 1 = raw` is invisible. -/
theorem k73_incr_machine_bytes_eq_written_keep
    {gasLimit gasUsed target : Word} {parentBytes A : List (BitVec 8)}
    (htgtDef : target.toNat = gasLimit.toNat / 2)
    (hlt : target.toNat < gasUsed.toNat)
    (htargetPos : 0 < target.toNat)
    (hleTarget : target.toNat ≤ 2 ^ 56)
    (hlenP : parentBytes.length = 32) (halenA : A.length = 32)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
        (gasUsed - target).toNat < 2 ^ 256)
    (hvalA : EvmAsm.Crypto.beBytesToNat A
        = (EvmAsm.Crypto.beBytesToNat parentBytes * (gasUsed - target).toNat)
          % 2 ^ 256)
    (hpNZ : EvmAsm.Crypto.beBytesToNat
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8) ≠ 0) :
    U256AddBeSAsm.u256AddBeBytes parentBytes
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8)
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8)
      = hvbfWrittenImage gasLimit gasUsed parentBytes := by
  have hdw : (gasUsed - target).toNat = gasUsed.toNat - target.toNat := by
    refine k73_incr_word_delta_toNat target gasUsed ?_
    omega
  rw [hdw] at hvalA hMulFit
  have hbB : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes
      = EvmAsm.Crypto.beBytesToNat parentBytes :=
    k73_bytesBEtoNat_eq_beBytesToNat parentBytes
  rw [hbB] at hMulFit
  have hval2 : EvmAsm.Crypto.beBytesToNat A
      = EvmAsm.Crypto.beBytesToNat parentBytes
        * (gasUsed.toNat - target.toNat) :=
    hvalA.trans (Nat.mod_eq_of_lt hMulFit)
  have hvq2 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.k73_decr_quot2_value A target htargetPos hleTarget halenA
  have hq1 := k73_quot_bytes_natToBytesBE A A target halenA halenA htargetPos hleTarget
  have hlq1 : (u256DivU64BeQuotBytes A A target).length = 32 := by
    rw [hq1]; simp
  have hq2 := k73_quot_bytes_natToBytesBE
      (u256DivU64BeQuotBytes A A target)
      (u256DivU64BeQuotBytes A A target) 8 hlq1 hlq1 (by decide) (by decide)
  have hlq2 : (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
      (u256DivU64BeQuotBytes A A target) 8).length = 32 := by
    rw [hq2]; simp
  -- raw as a numeral
  have hraw : EvmAsm.Crypto.beBytesToNat
      (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
        (u256DivU64BeQuotBytes A A target) 8)
      = EvmAsm.Crypto.beBytesToNat parentBytes
        * (gasUsed.toNat - target.toNat) / target.toNat / 8 := by
    rw [hvq2, hval2]
  rw [hraw] at hpNZ
  -- value of the machine output: truncated sum
  have hadd := U256BeFlat.beBytesToNat_u256AddBeBytes parentBytes
    (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
      (u256DivU64BeQuotBytes A A target) 8)
    (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
      (u256DivU64BeQuotBytes A A target) 8) hlenP hlq2 hlq2
  set Q2 := u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
    (u256DivU64BeQuotBytes A A target) 8 with hQ2
  have hbnd : EvmAsm.Crypto.beBytesToNat
      (U256AddBeSAsm.u256AddBeBytes parentBytes Q2 Q2) < 2 ^ 256 := by
    have hb := k73_fixed_bytes_bound
      (U256AddBeSAsm.u256AddBeBytes parentBytes Q2 Q2)
    rw [k73_bytesBEtoNat_eq_beBytesToNat,
      U256BeFlat.u256AddBeBytes_length parentBytes Q2 Q2 hlq2] at hb
    exact hb
  have elhs : EvmAsm.Crypto.beBytesToNat
      (U256AddBeSAsm.u256AddBeBytes parentBytes Q2 Q2)
      = (EvmAsm.Crypto.beBytesToNat parentBytes
          + EvmAsm.Crypto.beBytesToNat Q2) % 2 ^ 256 := by
    have key : ∀ a b : Nat, (a + 2 ^ 256 * b) % 2 ^ 256 = a % 2 ^ 256 := by
      intro a b
      rw [Nat.mul_comm ((2 : Nat) ^ 256) b, Nat.add_mul_mod_self_right]
    have estep := congrArg (fun n : Nat => n % 2 ^ 256) (hadd.symm)
    exact ((estep.trans (key _ _)).trans (Nat.mod_eq_of_lt hbnd)).symm
  -- value of the written image
  have erhs : EvmAsm.Crypto.beBytesToNat
      (hvbfWrittenImage gasLimit gasUsed parentBytes)
      = (EvmAsm.Crypto.beBytesToNat parentBytes
          + (EvmAsm.Crypto.beBytesToNat parentBytes
              * (gasUsed.toNat - target.toNat)) / target.toNat / 8)
        % 2 ^ 256 := by
    rw [k73_incr_written_val htgtDef hlt hlenP]
    -- max raw 1 = raw because raw != 0
    exact congrArg (fun n => (EvmAsm.Crypto.beBytesToNat parentBytes + n) % 2 ^ 256)
      (Nat.max_eq_left (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpNZ)))
  apply k73_bytes_inj_same_length
  · rw [U256BeFlat.u256AddBeBytes_length parentBytes Q2 Q2 hlq2]
    exact (hvbfWrittenImage_length gasLimit gasUsed parentBytes).symm
  · rw [erhs]
    rw [hraw] at elhs
    exact elhs


set_option maxRecDepth 8000 in
/-- Machine output on the increase REPLACE arm: the accumulator window is
    all zero (`raw = 0`), the machine replaces it with `u256_from_u64_be 1`,
    and the spec clamp makes the image `(fee + 1) mod 2^256`. -/
theorem k73_incr_machine_bytes_eq_written_replace
    {gasLimit gasUsed target : Word} {parentBytes A : List (BitVec 8)}
    (htgtDef : target.toNat = gasLimit.toNat / 2)
    (hlt : target.toNat < gasUsed.toNat)
    (htargetPos : 0 < target.toNat)
    (hleTarget : target.toNat ≤ 2 ^ 56)
    (hlenP : parentBytes.length = 32) (halenA : A.length = 32)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
        (gasUsed - target).toNat < 2 ^ 256)
    (hvalA : EvmAsm.Crypto.beBytesToNat A
        = (EvmAsm.Crypto.beBytesToNat parentBytes * (gasUsed - target).toNat)
          % 2 ^ 256)
    (hpZ : EvmAsm.Crypto.beBytesToNat
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8) = 0) :
    U256AddBeSAsm.u256AddBeBytes parentBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
      = hvbfWrittenImage gasLimit gasUsed parentBytes := by
  have hdw : (gasUsed - target).toNat = gasUsed.toNat - target.toNat := by
    refine k73_incr_word_delta_toNat target gasUsed ?_
    omega
  rw [hdw] at hvalA hMulFit
  have hbB : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes
      = EvmAsm.Crypto.beBytesToNat parentBytes :=
    k73_bytesBEtoNat_eq_beBytesToNat parentBytes
  rw [hbB] at hMulFit
  have hval2 : EvmAsm.Crypto.beBytesToNat A
      = EvmAsm.Crypto.beBytesToNat parentBytes
        * (gasUsed.toNat - target.toNat) :=
    hvalA.trans (Nat.mod_eq_of_lt hMulFit)
  have hvq2 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.k73_decr_quot2_value
    A target htargetPos hleTarget halenA
  have hraw : EvmAsm.Crypto.beBytesToNat
      (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
        (u256DivU64BeQuotBytes A A target) 8)
      = EvmAsm.Crypto.beBytesToNat parentBytes
        * (gasUsed.toNat - target.toNat) / target.toNat / 8 := by
    rw [hvq2, hval2]
  rw [hraw] at hpZ
  have hlen1 := U256FromU64BeSAsm.length_u256FromU64Bytes (1 : Word)
  have hval1 : EvmAsm.Crypto.beBytesToNat
      (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) = 1 := by
    rw [U256BeFlat.beBytesToNat_u256FromU64Bytes (1 : Word)]
    rfl
  have hadd := U256BeFlat.beBytesToNat_u256AddBeBytes parentBytes
    (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
    (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) hlenP hlen1 hlen1
  have hbnd : EvmAsm.Crypto.beBytesToNat
      (U256AddBeSAsm.u256AddBeBytes parentBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))) < 2 ^ 256 := by
    have hb := k73_fixed_bytes_bound
      (U256AddBeSAsm.u256AddBeBytes parentBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)))
    rw [k73_bytesBEtoNat_eq_beBytesToNat,
      U256BeFlat.u256AddBeBytes_length parentBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) hlen1] at hb
    exact hb
  have elhs : EvmAsm.Crypto.beBytesToNat
      (U256AddBeSAsm.u256AddBeBytes parentBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)))
      = (EvmAsm.Crypto.beBytesToNat parentBytes + 1) % 2 ^ 256 := by
    have key : ∀ a b : Nat, (a + 2 ^ 256 * b) % 2 ^ 256 = a % 2 ^ 256 := by
      intro a b
      rw [Nat.mul_comm ((2 : Nat) ^ 256) b, Nat.add_mul_mod_self_right]
    have t4 : (EvmAsm.Crypto.beBytesToNat parentBytes + 1) % 2 ^ 256
        = (EvmAsm.Crypto.beBytesToNat parentBytes
            + EvmAsm.Crypto.beBytesToNat
              (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))) % 2 ^ 256 := by
      rw [hval1]
    have t3 : (EvmAsm.Crypto.beBytesToNat parentBytes
          + EvmAsm.Crypto.beBytesToNat
            (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))) % 2 ^ 256
        = (EvmAsm.Crypto.beBytesToNat
            (U256AddBeSAsm.u256AddBeBytes parentBytes
              (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
              (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)))
          + 2 ^ 256 * (U256AddBeSAsm.u256AddBeCarry parentBytes
              (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
              (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))).toNat) % 2 ^ 256 := by
      rw [hadd]
    exact (((t4.trans t3).trans (key _ _)).trans
      (Nat.mod_eq_of_lt hbnd)).symm
  have erhs : EvmAsm.Crypto.beBytesToNat
      (hvbfWrittenImage gasLimit gasUsed parentBytes)
      = (EvmAsm.Crypto.beBytesToNat parentBytes + 1) % 2 ^ 256 := by
    have eval := k73_incr_written_val htgtDef hlt hlenP
    have hmax : Nat.max ((EvmAsm.Crypto.beBytesToNat parentBytes *
        (gasUsed.toNat - target.toNat)) / target.toNat / 8) 1 = 1 := by
      rw [hpZ]
      rfl
    exact eval.trans (congrArg
      (fun n => (EvmAsm.Crypto.beBytesToNat parentBytes + n) % 2 ^ 256) hmax)
  apply k73_bytes_inj_same_length
  · rw [U256BeFlat.u256AddBeBytes_length parentBytes
      (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
      (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) hlen1]
    exact (hvbfWrittenImage_length gasLimit gasUsed parentBytes).symm
  · rw [erhs]
    exact elhs

/-! ## Increase-arm Route-B junction casts -/

/-- Wrapper-side ambient atoms the machine exits omit (caller frame,
    header bytes, scratch registers) that the Route-B posts require. -/
private def k73_incr_piggyback (wspH old8 headerPtr : Word)
    (headerBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  frameSlotsSaved hvbfFrame wspH (hvbfSaved (H + 40) old8) **
    bytesRegion headerPtr headerBytes ** regOwn .x13 ** regOwn .x5 **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** F

/-- Window-content cast at the `Expected` cell. -/
private theorem k73_incr_br_cast {le le' : List (BitVec 8)} {Z : Assertion}
    (heq : le = le') :
    ∀ q, ((bytesRegion Expected le ** Z) q) → ((bytesRegion Expected le' ** Z) q) :=
  fun _ hp => heq ▸ hp

/-- Fixed exit junk that has no home in the Route-B post: the add scratch
    registers, the multiply scratch frame, and the multiply accumulator
    window.  Absorbed into the universally quantified trailing slot. -/
private def k73_incr_outj (wspK parentPtr gasUsed target : Word)
    (_parentBytes A : List (BitVec 8)) (F : Assertion) : Assertion :=
  regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch **
    U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
      parentPtr Expected target (gasUsed - target) (1 : Word) **
    bytesRegion U256MulU64Be.accBase A ** F

/-- First-arm junction cast: the add has run, its output sits at `Expected`,
    and the BEQZ outcome has been folded into the status register.
    `x10 = 0` is the success arm (image cast by the keep W-equality);
    `x10 = 1` is the failure arm (the image is the scratch content). -/
private theorem k73_incr_first_routeB
    (wspH wspK old8 headerPtr parentPtr v9 old18 v19 v20 gasUsed target : Word)
    (parentBytes A q2 headerBytes : List (BitVec 8)) (Frest : Assertion)
    (hcast : U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2
      = hvbfWrittenImage gasLimit gasUsed parentBytes) :
    ∀ s, (k73IncreaseFirstFinalPost wspH wspK (H + 40) gasUsed parentPtr Expected
        target headerPtr v9 old18 v19 v20 parentBytes A q2
        (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)) s →
    (((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost wspH wspK (H + 40) old8 headerPtr
        v9 old18 target v19 v20 gasUsed gasLimit parentPtr parentBytes
        headerBytes
        (k73_incr_outj wspK parentPtr gasUsed target parentBytes A Frest)) s)  := by
  intro s hp
  simp only [k73IncreaseFirstFinalPost] at hp
  rcases hp with h1 | h0
  · -- failure disjunct (x10 = 1)
    have hEq1 : (((.x2 : Reg) ↦ᵣ wspH) ** ((regsAt k73Frame (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))
        = (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) := by
      simp only [k73Frame, regsAt_cons, regsAt_nil, k73Saved, sepConj_emp_right']
      xperm_cert_eq
    have hp1 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      hEq1 ▸ h1
    have hc11 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((regOwn .x11) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (1 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x11) (v := Expected))) s hp1
    have hc12 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (1 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x12) (v := Expected)))) s hc11
    have hEq2 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))))
        = (((.x1 : Reg) ↦ᵣ (H + 40)) ** (k73FailurePost wspH wspK headerPtr v9
            old18 target v19 v20 gasUsed parentPtr (1 : Word) parentBytes
            (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2) headerBytes
            (H + 40) old8
            (k73_incr_outj wspK parentPtr gasUsed target parentBytes A Frest))) := by
      dsimp only [k73FailurePost, tailRestScratch, tailRestCore, k73_incr_piggyback,
        k73_incr_outj]
      xperm_cert_eq
    have hcb := hEq2 ▸ hc12
    obtain ⟨sa, sb, had, hud, hx1, hFP⟩ := hcb
    exact ⟨sa, sb, had, hud, hx1,
      Or.inr ⟨(1 : Word), U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2, by decide, hFP⟩⟩
  · -- success disjunct (x10 = 0)
    have hEq1 : (((.x2 : Reg) ↦ᵣ wspH) ** ((regsAt k73Frame (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))
        = (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) := by
      simp only [k73Frame, regsAt_cons, regsAt_nil, k73Saved, sepConj_emp_right']
      xperm_cert_eq
    have hp1 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      hEq1 ▸ h0
    have hc11 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((regOwn .x11) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (0 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x11) (v := Expected))) s hp1
    have hc12 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes q2 q2)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (0 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x12) (v := Expected)))) s hc11
    have hcbr : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (0 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x12) (k73_incr_br_cast hcast)))) s hc12
    have hcl : ((((.x2 : Reg) ↦ᵣ wspH) ** ((regOwn .x10) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x10) (v := (0 : Word))) s hcbr
    have hEq2 : (((.x2 : Reg) ↦ᵣ wspH) ** ((regOwn .x10) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))))
        = (((.x1 : Reg) ↦ᵣ (H + 40)) ** (k73PostOwn wspH wspK headerPtr v9 old18
            target v19 v20 gasUsed parentPtr parentBytes
            (hvbfWrittenImage gasLimit gasUsed parentBytes) headerBytes
            (H + 40) old8
            (k73_incr_outj wspK parentPtr gasUsed target parentBytes A Frest))) := by
      dsimp only [k73PostOwn, tailRest, tailRestCore, k73_incr_piggyback,
        k73_incr_outj]
      xperm_cert_eq
    have hcb := hEq2 ▸ hcl
    obtain ⟨sa, sb, had, hud, hx1, hPO⟩ := hcb
    exact ⟨sa, sb, had, hud, hx1, Or.inl hPO⟩

/-- First-arm junction cast: the add has run, its output sits at `Expected`,
    and the BEQZ outcome has been folded into the status register.
    `x10 = 0` is the success arm (image cast by the keep W-equality);
    `x10 = 1` is the failure arm (the image is the scratch content). -/
private theorem k73_incr_second_routeB
    (wspH wspK old8 headerPtr parentPtr v9 old18 v19 v20 gasUsed target : Word)
    (parentBytes A orig headerBytes : List (BitVec 8)) (Frest : Assertion)
    (hcast : U256AddBeSAsm.u256AddBeBytes parentBytes orig orig
      = hvbfWrittenImage gasLimit gasUsed parentBytes) :
    ∀ s, (k73IncreaseSecondFinalPost wspH wspK (H + 40) gasUsed parentPtr Expected
        target headerPtr v9 old18 v19 v20 parentBytes A orig
        (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)) s →
    (((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost wspH wspK (H + 40) old8 headerPtr
        v9 old18 target v19 v20 gasUsed gasLimit parentPtr parentBytes
        headerBytes
        (k73_incr_outj wspK parentPtr gasUsed target parentBytes A Frest)) s)  := by
  intro s hp
  simp only [k73IncreaseSecondFinalPost] at hp
  rcases hp with h1 | h0
  · -- failure disjunct (x10 = 1)
    have hEq1 : (((.x2 : Reg) ↦ᵣ wspH) ** ((regsAt k73Frame (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))
        = (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) := by
      simp only [k73Frame, regsAt_cons, regsAt_nil, k73Saved, sepConj_emp_right']
      xperm_cert_eq
    have hp1 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      hEq1 ▸ h1
    have hc11 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((regOwn .x11) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (1 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x11) (v := Expected))) s hp1
    have hc12 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (1 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x12) (v := Expected)))) s hc11
    have hEq2 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))))
        = (((.x1 : Reg) ↦ᵣ (H + 40)) ** (k73FailurePost wspH wspK headerPtr v9
            old18 target v19 v20 gasUsed parentPtr (1 : Word) parentBytes
            (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig) headerBytes
            (H + 40) old8
            (k73_incr_outj wspK parentPtr gasUsed target parentBytes A Frest))) := by
      dsimp only [k73FailurePost, tailRestScratch, tailRestCore, k73_incr_piggyback,
        k73_incr_outj]
      xperm_cert_eq
    have hcb := hEq2 ▸ hc12
    obtain ⟨sa, sb, had, hud, hx1, hFP⟩ := hcb
    exact ⟨sa, sb, had, hud, hx1,
      Or.inr ⟨(1 : Word), U256AddBeSAsm.u256AddBeBytes parentBytes orig orig, by decide, hFP⟩⟩
  · -- success disjunct (x10 = 0)
    have hEq1 : (((.x2 : Reg) ↦ᵣ wspH) ** ((regsAt k73Frame (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))
        = (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) := by
      simp only [k73Frame, regsAt_cons, regsAt_nil, k73Saved, sepConj_emp_right']
      xperm_cert_eq
    have hp1 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (((.x11 : Reg) ↦ᵣ Expected) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      hEq1 ▸ h0
    have hc11 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((regOwn .x11) ** (((.x12 : Reg) ↦ᵣ Expected) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (0 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x11) (v := Expected))) s hp1
    have hc12 : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (U256AddBeSAsm.u256AddBeBytes parentBytes orig orig)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (0 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x12) (v := Expected)))) s hc11
    have hcbr : (((.x2 : Reg) ↦ᵣ wspH) ** (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 : Reg) ↦ᵣ (0 : Word)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x12) (k73_incr_br_cast hcast)))) s hc12
    have hcl : ((((.x2 : Reg) ↦ᵣ wspH) ** ((regOwn .x10) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))))) s :=
      EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 : Reg) ↦ᵣ wspH) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x10) (v := (0 : Word))) s hcbr
    have hEq2 : (((.x2 : Reg) ↦ᵣ wspH) ** ((regOwn .x10) ** ((regOwn .x11) ** ((regOwn .x12) ** ((bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes)) ** (((.x1 : Reg) ↦ᵣ (H + 40)) ** (((.x8 : Reg) ↦ᵣ headerPtr) ** (((.x9 : Reg) ↦ᵣ v9) ** (((.x18 : Reg) ↦ᵣ old18) ** (((.x19 : Reg) ↦ᵣ v19) ** (((.x20 : Reg) ↦ᵣ v20) ** ((frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) ** (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** ((bytesRegion parentPtr parentBytes) ** ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word)) ** ((bytesRegion U256MulU64Be.accBase A) ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))))
        = (((.x1 : Reg) ↦ᵣ (H + 40)) ** (k73PostOwn wspH wspK headerPtr v9 old18
            target v19 v20 gasUsed parentPtr parentBytes
            (hvbfWrittenImage gasLimit gasUsed parentBytes) headerBytes
            (H + 40) old8
            (k73_incr_outj wspK parentPtr gasUsed target parentBytes A Frest))) := by
      dsimp only [k73PostOwn, tailRest, tailRestCore, k73_incr_piggyback,
        k73_incr_outj]
      xperm_cert_eq
    have hcb := hEq2 ▸ hcl
    obtain ⟨sa, sb, had, hud, hx1, hPO⟩ := hcb
    exact ⟨sa, sb, had, hud, hx1, Or.inl hPO⟩

/-- Junk the increase mul-overflow failure exit leaves behind: the multiply
    scratch frame, the overflow window core (parameterised by the window
    index), and the scratch registers neither the epilogue nor the wrapper
    reclaims. -/
private def k73_incr_carry_junk (wspK parentPtr gasUsed target : Word)
    (A : List (BitVec 8)) (k : Nat) (Frest : Assertion) : Assertion :=
  U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** k73MulOverflowCoreNoStatus A k **
    regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    Frest

/-- Route-B cast for the increase mul-overflow (carry) failure arm: the
    status-1 exit folds into the failure disjunct with `outBytes` as the
    scratch image and the overflow window's index `k` threaded through the
    junk. -/
private theorem k73_incr_carry_routeB_fail
    (wspH wspK old8 headerPtr parentPtr v9 old18 v19 v20 gasUsed target : Word)
    (parentBytes A outBytes headerBytes : List (BitVec 8)) (Frest : Assertion) :
    ∀ s : PartialState,
        (k73IncreaseCarryFinalPost wspH wspK (H + 40) gasUsed parentPtr Expected target headerPtr v9 old18 v19 v20 parentBytes A outBytes (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)) s →
        (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
            (scratchBytes : List (BitVec 8)) (k : Nat), status ≠ (0 : Word) ∧
              k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
                parentPtr status parentBytes scratchBytes headerBytes
                (H + 40) old8 (k73_incr_carry_junk wspK parentPtr gasUsed target A k Frest) u)) s) := by
  intro s hp
  have hEq1 : (k73IncreaseCarryFinalPost wspH wspK (H + 40) gasUsed parentPtr Expected target headerPtr v9 old18 v19 v20 parentBytes A outBytes (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)) = ((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (gasUsed - target) Expected parentBytes ** ((fun u => ∃ k, (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k) u) ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))) := by
    simp only [k73IncreaseCarryFinalPost, k73IncreaseCarryTail, k73Frame,
      regsAt_cons, regsAt_nil, k73Saved, sepConj_emp_right', regOwns_cons,
      regOwns_nil]
    xperm_cert_eq
  have hp1 : (((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (gasUsed - target) Expected parentBytes ** ((fun u => ∃ k, (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k) u) ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) s := hEq1 ▸ hp
  have hrot : (((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (gasUsed - target) Expected parentBytes ** ((fun u => ∃ k, (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k) u) ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))) =
      (((fun u => ∃ k, (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k) u)) ** ((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (gasUsed - target) Expected parentBytes ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))) := by
    xperm_cert_eq
  obtain ⟨k, hk⟩ := (sepConj_exists_left s).mp (hrot ▸ hp1)
  have hE : ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k)) ** ((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (gasUsed - target) Expected parentBytes ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))) =
      ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k)) ** ((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (bytesRegion parentPtr parentBytes ** ((.x7 ↦ᵣ (0 : Word)) ** ((.x11 ↦ᵣ (gasUsed - target)) ** ((.x12 ↦ᵣ Expected) ** (regOwn .x13 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))))))))) := by
    dsimp only [EvmAsm.Codegen.U256MulU64Be.mulTailExtra]
    xperm_cert_eq
  have hk0X : ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k)) ** ((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (bytesRegion parentPtr parentBytes ** ((.x7 ↦ᵣ (0 : Word)) ** ((.x11 ↦ᵣ (gasUsed - target)) ** ((.x12 ↦ᵣ Expected) ** (regOwn .x13 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))))))))) s := hE ▸ hk
  have hkEq : ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion Expected outBytes ** k73MulOverflowCoreNoStatus A k)) ** ((.x2 ↦ᵣ wspH) ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (bytesRegion parentPtr parentBytes ** ((.x7 ↦ᵣ (0 : Word)) ** ((.x11 ↦ᵣ (gasUsed - target)) ** ((.x12 ↦ᵣ Expected) ** (regOwn .x13 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))))))))) =
      ((.x2 ↦ᵣ wspH) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** ((.x7 ↦ᵣ (0 : Word)) ** ((.x11 ↦ᵣ (gasUsed - target)) ** ((.x12 ↦ᵣ Expected) ** (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion Expected outBytes ** (k73MulOverflowCoreNoStatus A k ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** (regOwn .x13 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (bytesRegion parentPtr parentBytes ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))))))))))) := by
    xperm_cert_eq
  have hk0 : ((.x2 ↦ᵣ wspH) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** ((.x7 ↦ᵣ (0 : Word)) ** ((.x11 ↦ᵣ (gasUsed - target)) ** ((.x12 ↦ᵣ Expected) ** (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion Expected outBytes ** (k73MulOverflowCoreNoStatus A k ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** (regOwn .x13 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (bytesRegion parentPtr parentBytes ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest)))))))))))))))))))))))))) s := by
    have hx := hk0X
    rw [hkEq] at hx
    exact hx
  have hc7 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 ↦ᵣ wspH)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 ↦ᵣ (1 : Word))) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x0 ↦ᵣ (0 : Word))) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x7) (v := (0 : Word))))) s hk0
  have hc11 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 ↦ᵣ wspH)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 ↦ᵣ (1 : Word))) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x0 ↦ᵣ (0 : Word))) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x7) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x11) (v := (gasUsed - target)))))) s hc7
  have hc12 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 ↦ᵣ wspH)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 ↦ᵣ (1 : Word))) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x0 ↦ᵣ (0 : Word))) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x7) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x12) (v := Expected)))))) s hc11
  have hEq2 : (((.x2 ↦ᵣ wspH) ** ((.x10 ↦ᵣ (1 : Word)) ** ((.x0 ↦ᵣ (0 : Word)) ** (regOwn .x7 ** (regOwn .x11 ** (regOwn .x12 ** (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion Expected outBytes ** (k73MulOverflowCoreNoStatus A k ** ((.x1 ↦ᵣ (H + 40)) ** ((.x8 ↦ᵣ headerPtr) ** ((.x9 ↦ᵣ v9) ** ((.x18 ↦ᵣ old18) ** ((.x19 ↦ᵣ v19) ** ((.x20 ↦ᵣ v20) ** (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) ** (regOwn .x13 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (bytesRegion parentPtr parentBytes ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** (k73_incr_piggyback wspH old8 headerPtr headerBytes Frest))))))))))))))))))))))))))) =
      (((.x1 ↦ᵣ (H + 40)) ** k73FailurePost wspH wspK headerPtr v9 old18
        target v19 v20 gasUsed parentPtr (1 : Word) parentBytes outBytes
        headerBytes (H + 40) old8 (k73_incr_carry_junk wspK parentPtr gasUsed target A k Frest))) := by
    dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
      k73_incr_piggyback, k73_incr_carry_junk]
    xperm_cert_eq
  obtain ⟨sa, sb, had, hud, hx1, hFP⟩ := hEq2 ▸ hc12
  exact ⟨sa, sb, had, hud, hx1, ⟨(1 : Word), outBytes, k, by decide, hFP⟩⟩



end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute
