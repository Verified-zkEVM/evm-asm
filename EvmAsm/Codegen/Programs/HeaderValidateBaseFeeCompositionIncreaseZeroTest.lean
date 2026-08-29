/-
  Increase-arm zero-test seam toward the Route-B K73 contract (#12346 item 2b).

  The merged increase-route final post drops the runtime is-zero fact that
  decides which clamp path the machine took, so the Route-B adapter assembles
  from seams and threads the fact through.  This file carries the zero-test
  portion: the window-value zero-test algebra, the strengthened is_zero call
  spec whose result is valued, the zero-branch register facts, and the
  keep/replace case theorems that give the written image on each clamp path
  (`parentFee + raw` versus `parentFee + 1`).
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

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseZeroTest

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
    ∀ old10, cpsTripleWithin 11 (K73 + 132) (K73 + 140) wholeCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ ptr) **
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
  have hmvAny : cpsTripleWithin 1 (K73 + 132) (K73 + 136) wholeCode
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
    have hmv := mv_spec_gen_within .x10 .x9 ptr old10 (K73 + 132) (by decide)
    have hmvC := cpsTripleWithin_extend_code
      (k73_whole_mem 33 _ (K73 + 132) (by decide)
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
      (K73 + 136) + signExtend21
        (jalOff GuestAddrs.u256_is_zero
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 136)) =
        (GuestAddrs.u256_is_zero : Word) := by
    change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 136 + _ = BitVec.ofNat 64 GuestAddrs.u256_is_zero
    exact jalOff_correct_add GuestAddrs.u256_is_zero
      GuestAddrs.eip1559_calc_base_fee_per_gas 136
      (by decide) (by decide) (by decide) (by decide)
  have hmem : ∀ a i, CodeReq.singleton (K73 + 136)
      (.JAL .x1 (jalOff GuestAddrs.u256_is_zero
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 136))) a = some i →
      wholeCode a = some i := by
    intro a i hi
    exact k73_whole_mem 34 _ (K73 + 136) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi
  have hcallAny : ∀ vf : Reg → Word,
      cpsTripleWithin 10 (K73 + 136) (K73 + 140) wholeCode
      (((((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regAtomsOf vf u256DivU64BeScratch))
      (((((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
          (1 : Word) else 0)) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regOwns u256DivU64BeScratch)) := by
    intro vf
    have hzero := u256IsZeroFlat_spec_domain ptr (K73 + 140)
      (vf .x5) (vf .x6) (vf .x7) (vf .x28) w0 w1 w2 w3
    have hzeroC := cpsTripleWithin_extend_code isZero_whole_mono hzero
    have hP0 : (((.x10 : Reg) ↦ᵣ ptr) **
        ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
        ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3))).pcFree := by
      pcf
    have hcallee0 : cpsTripleWithin 9 (GuestAddrs.u256_is_zero : Word)
        (K73 + 140) wholeCode
        (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x10 : Reg) ↦ᵣ ptr) **
          ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)))
        (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
      (K73 + 136) (GuestAddrs.u256_is_zero : Word) oldRa
      (jalOff GuestAddrs.u256_is_zero
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 136)) 9 htarget hmem hP0 hcallee0
    have hcallF := cpsTripleWithin_frameR
      (regAtomsOf vf tail ** F) (by dsimp [tail]; pcf; exact hF) hcall0
    have hcall : cpsTripleWithin 10 (K73 + 136) (K73 + 140) wholeCode
        (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
          ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
          ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
          regAtomsOf vf tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F)
        (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
          ((.x10 : Reg) ↦ᵣ (if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then
            (1 : Word) else 0)) **
          ((.x5 : Reg) ↦ᵣ (w0 ||| w1 ||| w2 ||| w3)) **
          ((.x6 : Reg) ↦ᵣ w1) ** ((.x7 : Reg) ↦ᵣ w2) **
          ((.x28 : Reg) ↦ᵣ w3) ** regAtomsOf vf tail **
          ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
            ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) := by
      simpa only [show 1 + 9 = 10 by decide, sepConj_assoc', sepConj_comm',
        sepConj_left_comm',
        show (K73 + 136) + 4 = K73 + 140 by bv_omega] using hcallF
    exact cpsTripleWithin_weaken
      (P' := (((.x1 : Reg) ↦ᵣ oldRa) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((ptr ↦ₘ w0) ** ((ptr + 8) ↦ₘ w1) **
          ((ptr + 16) ↦ₘ w2) ** ((ptr + 24) ↦ₘ w3)) ** F) **
        regAtomsOf vf u256DivU64BeScratch)
      (Q' := (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
            (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
    (Q := ((((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
    (Q' := (((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ ptr) **
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
    ∀ old10 : Word, cpsBranchWithin 1 (K73 + 140) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 176)
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜old10 = (0 : Word)⌝)
      (K73 + 144)
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ old10)) **
        ⌜old10 ≠ (0 : Word)⌝) := by
  intro old10
  let Base : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 140)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F
  let Rest : Assertion := ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Base
  have hBase : Base.pcFree := by
    dsimp [Base]
    pcf
    exact hF
  have hbeq := beq_spec_gen_within .x10 .x0 (36 : BitVec 13)
    old10 (0 : Word) (K73 + 140)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 35 _ (K73 + 140) (by decide)
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
          ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
          ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
    cpsTripleWithin 1 (K73 + 140) (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ (if packBytes ((q2.drop 0).take 8) = 0 ∧
            packBytes ((q2.drop 8).take 8) = 0 ∧
            packBytes ((q2.drop 16).take 8) = 0 ∧
            packBytes ((q2.drop 24).take 8) = 0 then (1 : Word) else 0)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
  have h_t0 : cpsTripleWithin 0 (K73 + 176) (K73 + 176) CodeReq.empty
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(0 : Word) = (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F) :=
    cpsTripleWithin_refl (fun _ h => by
      obtain ⟨hq, _⟩ := (sepConj_pure_right _).1 h
      xperm_hyp hq)
  have h_t : cpsTripleWithin 0 (K73 + 176) (K73 + 176) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(0 : Word) = (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F) :=
    cpsTripleWithin_extend_code (cr' := wholeCode)
      (fun a i hi => by simp [CodeReq.empty] at hi) h_t0

  have h_f : cpsTripleWithin 0 (K73 + 144) (K73 + 176) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(0 : Word) ≠ (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
      (K73 + 140) (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ (if packBytes ((q2.drop 0).take 8) = 0 ∧
            packBytes ((q2.drop 8).take 8) = 0 ∧
            packBytes ((q2.drop 16).take 8) = 0 ∧
            packBytes ((q2.drop 24).take 8) = 0 then (1 : Word) else 0)) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
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
      (K73 + 176) (K73 + 176) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) **
        ⌜(1 : Word) = (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** regOwns exposedRegs **
        bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) := by
    intro R hR s hcr hPR hpc
    obtain ⟨h, hcompat, h1, h2, hd, hu, hpl, hpr⟩ := hPR
    obtain ⟨_, hz⟩ := (sepConj_pure_right _).1 hpl
    exact absurd hz (by decide)
  have h_f : cpsTripleWithin
      (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1)
      (K73 + 144) (K73 + 176) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F) ** ((.x10 : Reg) ↦ᵣ (1 : Word))) **
        ⌜(1 : Word) ≠ (0 : Word)⌝)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 156)) **
        ((.x9 : Reg) ↦ᵣ ptr) ** regOwns exposedRegs **
        bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) := by
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hq => hq) hf0
    obtain ⟨hpair, _⟩ := (sepConj_pure_right _).1 hp
    have hmid : (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
        (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (((.x9 : Reg) ↦ᵣ ptr) **
        (((.x11 : Reg) ↦ᵣ (8 : Word)) ** (((.x12 : Reg) ↦ᵣ ptr) **
        (regOwns u256DivU64BeScratch ** (bytesRegion ptr q2 ** F)))))))) s := by
      xperm_hyp hpair
    have hl3 : (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (((.x1 : Reg) ↦ᵣ (K73 + 140)) **
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
