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
    header bytes) that the Route-B posts require.  The scratch set the
    wrapper spine already owns (`x5 x6 x7 x13 x28 x29 x30 x31`) is
    deliberately NOT here: duplicating an exact `regOwn` atom makes the
    assertion unsatisfiable (each atom pins its singleton cell exactly). -/
private def k73_incr_piggyback (wspH old8 headerPtr : Word)
    (headerBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  frameSlotsSaved hvbfFrame wspH (hvbfSaved (H + 40) old8) **
    bytesRegion headerPtr headerBytes ** F

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



/-- Threaded multiply output image: the post-mul window the divider reads
(token form of the computed lists; the plain term whnf-diverges when
elaborated inline against route binders). -/
private def k73_incr_outT (parentBytes : List (BitVec 8)) (delta : Word)
    (outWin : List (BitVec 8)) : List (BitVec 8) :=
  EvmAsm.Codegen.U256MulU64Be.copyState
    (EvmAsm.Codegen.U256MulU64Be.mulState parentBytes delta 32) outWin 32

/-- Token form of the double-quotient windows (plain inline spellings whnf-diverge
    when elaborated against the increase route binders). -/
private def k73_incr_q1 (TOK : List (BitVec 8)) (target : Word) : List (BitVec 8) :=
  u256DivU64BeQuotBytes TOK TOK target

private def k73_incr_q2 (TOK : List (BitVec 8)) (target : Word) : List (BitVec 8) :=
  u256DivU64BeQuotBytes (k73_incr_q1 TOK target) (k73_incr_q1 TOK target) 8


/-- Ambient envelope for the increase adapter premise: everything the
    wrapper world owns around the route (multiply scratch window, multiply
    callee-saved registers, and the trailing envelope `F`).  The registers
    the route's own spine pins (`x8 x9 x18 x19 x20`) and the scratch set the
    spine already owns (`x5 x6 x7 x13 x28 x29 x30 x31`) are deliberately NOT
    here: duplicating an exact `regOwn` atom makes the premise unsatisfiable
    (each atom pins its singleton cell exactly). -/
private def k73_incr_env (wspK : Word) (f0 f1 f2 f3 f4 f5 : Word)
    (accWin : List (BitVec 8)) (F : Assertion) : Assertion :=
  U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12))
    f0 f1 f2 f3 f4 f5 ** bytesRegion U256MulU64Be.accBase accWin **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** F

/-- The increase route's taken leg is vacuous under `0 < target.toNat`
    (the div-zero status exit is unreachable), so the two-leg branch with
    `fun _ => False` as the taken post is exactly a single-exit triple. -/
private theorem k73_incr_branch_to_triple
    {n : Nat} {entry pt exitf : Word} {cr : CodeReq} {P Qf : Assertion}
    (h : cpsBranchWithin n entry cr P pt (fun _ => False) exitf Qf) :
    cpsTripleWithin n entry exitf cr P Qf := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  rcases hbranch with ⟨hpc', hQR⟩ | ⟨hpc', hQR⟩
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    obtain ⟨h1, h2, hd, hu, hl, hr⟩ := hhold
    exact hl.elim
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    exact ⟨hpc', hst, hcomp, hhold⟩


/-- Kill the window-index binder in the carry failure arm: the overflow
    core's `k`-dependent register pins lift into ownerships, leaving the
    `k`-free exit junk (exactly the `k73_incr_outj` body). -/
private theorem k73_incr_arm_unify
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 _gasLimit gasUsed target : Word)
    (parentBytes A _outWin headerBytes : List (BitVec 8)) (Frest : Assertion) :
    ∀ s : PartialState,
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)) (k : Nat),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed parentPtr status parentBytes scratchBytes headerBytes (H + 40) old8 (k73_incr_carry_junk wspK parentPtr gasUsed target A k Frest) u)) s) →
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed parentPtr status parentBytes scratchBytes headerBytes (H + 40) old8 ((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion U256MulU64Be.accBase A ** Frest))) u)) s) := by
  intro s hp
  obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hp
  obtain ⟨st, scr, k, hne, hFP⟩ := harm
  refine ⟨sa, sb, had, hud, hx1, ⟨st, scr, hne, ?_⟩⟩
  dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
    k73_incr_carry_junk, k73MulOverflowCoreNoStatus] at hFP ⊢
  have hR : ∀ q : PartialState,
      ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (((.x5 ↦ᵣ (U256MulU64Be.accBase + BitVec.ofNat 64 (32 + k))) ** ((.x6 ↦ᵣ BitVec.ofNat 64 (8 - k)) ** (regOwn .x28 ** bytesRegion U256MulU64Be.accBase A))) ** (regOwn .x13 ** (regOwn .x7 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** Frest)))))))))))) q →
      (((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion U256MulU64Be.accBase A ** Frest)))) q := by
    intro q hq
    have t1 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id
      (B := U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word))
      (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pair_congr
        (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x5)
          (v := U256MulU64Be.accBase + BitVec.ofNat 64 (32 + k)))
        (fun _ h => h)) q hq
    have t2 := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id
      (B := U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word))
      (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pair_congr
        (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pair_congr (fun _ h => h)
          (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_sep_pin_lift (r := Reg.x6) (v := BitVec.ofNat 64 (8 - k))))
        (fun _ h => h)) q t1
    have hE : ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** ((regOwn .x5 ** (regOwn .x6 ** (regOwn .x28 ** bytesRegion U256MulU64Be.accBase A))) ** (regOwn .x13 ** (regOwn .x7 ** (regOwn .x29 ** (regOwn .x30 ** (regOwn .x31 ** (regOwn .x14 ** (regOwn .x15 ** (regOwn .x16 ** (regOwn .x17 ** Frest)))))))))))) =
        (((regOwns EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch) ** (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88) parentPtr Expected target (gasUsed - target) (1 : Word) ** (bytesRegion U256MulU64Be.accBase A ** Frest)))) := by
      simp only [EvmAsm.Codegen.U256AddBeBInPlaceSAsm.u256AddBeBInPlaceScratch, regOwns_cons, regOwns_nil, sepConj_emp_right']
      xperm_cert_eq
    exact hE ▸ t2
  have hc := EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x2 ↦ᵣ wspH)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x8 ↦ᵣ headerPtr)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x10 ↦ᵣ st)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x11) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x0 ↦ᵣ (0 : Word))) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := frameSlotsSaved hvbfFrame wspH (hvbfSaved (H + 40) old8)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x9 ↦ᵣ v9)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x18 ↦ᵣ old18)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x19 ↦ᵣ v19)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := (.x20 ↦ᵣ v20)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x12) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x13) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x5) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x6) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x7) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x28) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x29) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x30) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := regOwn .x31) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20)) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := bytesRegion headerPtr headerBytes) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := bytesRegion parentPtr parentBytes) (EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute.decr_under_id (B := bytesRegion Expected scr) (hR))))))))))))))))))))))) sb hFP
  exact hc


/-- Isolated consumption of the increase whole route: the raw 58-argument
application lives in its own declaration so its elaboration cost does not
sum with the adapter's. -/
private theorem k73_incr_hw_bridge

    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (F : Assertion)
    (Nstatus Ntail : Nat)
    (hG : F.pcFree)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hlt : target.toNat < gasUsed.toNat)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F))
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F)))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hq1 : q1 = u256DivU64BeQuotBytes outBytes outBytes target)
    (hq2 : q2 = u256DivU64BeQuotBytes q1 q1 8)
    (hlen1 : q1.length = 32) (hlen2 : q2.length = 32)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAddQ2 : k73AddBSize basePtr outPtr baseBytes q2 ≤ 2 ^ 64)
    (hszAddOne : k73AddBSize basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4)
    (hNstatus : Nstatus =
      3857 + (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps
            + 1)) + 1)))))
    (hNq2 : 1 + k73AddBTailSteps basePtr outPtr baseBytes q2 ≤ Ntail)
    (hNq1 : 1 + k73AddBTailSteps basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ Ntail)
    (hNcarry : 9 ≤ Ntail) :
    cpsBranchWithin (13 + Nstatus + Ntail) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes **
          (regOwns [.x14, .x15, .x16, .x17] ** F)))
      (K73 + 204) (fun _ => False) raIn
      (k73IncreaseStatusFinalPost sp0 spH raIn gasUsed
        basePtr outPtr target v8 v9 v18 v19 v20
        baseBytes accBytes outBytes q2 F)  :=
  k73_increase_entry_status_div_zero_to_return_general_spec_within
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes q1 q2
    F Nstatus Ntail
    hG hsp htarget hne hlt hret hsaved hcallee hrw hlenOut hq1 hq2 hlen1 hlen2
    hovOut htargetPos hsz1 hsz2 hret1 hret2 hroBase hlenBase hovBase hdisj
    hszAddQ2 hszAddOne hcallRet hNstatus hNq2 hNq1 hNcarry

private theorem k73_incr_hw_triple
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (F : Assertion)
    (Nstatus Ntail : Nat)
    (hG : F.pcFree)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hlt : target.toNat < gasUsed.toNat)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F))
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F)))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hq1 : q1 = u256DivU64BeQuotBytes outBytes outBytes target)
    (hq2 : q2 = u256DivU64BeQuotBytes q1 q1 8)
    (hlen1 : q1.length = 32) (hlen2 : q2.length = 32)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAddQ2 : k73AddBSize basePtr outPtr baseBytes q2 ≤ 2 ^ 64)
    (hszAddOne : k73AddBSize basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4)
    (hNstatus : Nstatus =
      3857 + (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps
            + 1)) + 1)))))
    (hNq2 : 1 + k73AddBTailSteps basePtr outPtr baseBytes q2 ≤ Ntail)
    (hNq1 : 1 + k73AddBTailSteps basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ Ntail)
    (hNcarry : 9 ≤ Ntail) :
    cpsTripleWithin (13 + Nstatus + Ntail) K73 raIn wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes **
          (regOwns [.x14, .x15, .x16, .x17] ** F)))
      (k73IncreaseStatusFinalPost sp0 spH raIn gasUsed
        basePtr outPtr target v8 v9 v18 v19 v20
        baseBytes accBytes outBytes q2 F)
  := cpsTripleWithin_extend_code (fun _ _ h => h) (k73_incr_branch_to_triple (k73_incr_hw_bridge
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes q1 q2
    F Nstatus Ntail
    hG hsp htarget hne hlt hret hsaved hcallee hrw hlenOut hq1 hq2 hlen1 hlen2
    hovOut htargetPos hsz1 hsz2 hret1 hret2 hroBase hlenBase hovBase hdisj
    hszAddQ2 hszAddOne hcallRet hNstatus hNq2 hNq1 hNcarry
    ))

private theorem k73_incr_pre_eq
    (spH spK headerPtr old8 gasLimit gasUsed parentPtr v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes accWin : List (BitVec 8))
    (f0 f1 f2 f3 f4 f5 : Word) (F : Assertion) : ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes (H + 40) old8 (k73_incr_env spK f0 f1 f2 f3 f4 f5 accWin F)) =
      k73HeadPre spH spK (H + 40) gasLimit gasUsed parentPtr Expected
        headerPtr v9 old18 v19 v20 parentBytes expectedBytes
        (EvmAsm.Codegen.U256MulU64Be.frameSlots (spK + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 ** bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x17 ** k73_incr_piggyback spH old8 headerPtr headerBytes F) := by
    dsimp only [k73HeadPre, k73PreRest]
    dsimp only [k73_incr_env, k73_incr_piggyback]
    xperm

/-- The increase funnel in isolation: consumes the whole-route triple over
    the `k73HeadPre`/`k73IncreaseStatusFinalPost` spelling and the premise
    equality, and produces the wrapper-vocabulary Route-B conclusion over
    `wholeCode`.  Kept in its own declaration so its elaboration budget is
    not shared with the 58-argument hw application in the adapter. -/
private theorem k73_incr_funnel_close
    (spH spK old8 headerPtr parentPtr gasLimit gasUsed : Word)
    (v9 old18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (parentBytes expectedBytes headerBytes accWin outWin : List (BitVec 8))
    (F : Assertion) (Nstatus Ntail : Nat)
    (hbranch : cpsTripleWithin (13 + Nstatus + Ntail) K73 (H + 40) wholeCode
      (k73HeadPre spH spK (H + 40) gasLimit gasUsed parentPtr Expected
        headerPtr v9 old18 v19 v20 parentBytes
        (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)
        (U256MulU64Be.frameSlots (spK + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accWin **
          (regOwns [.x14, .x15, .x16, .x17] **
            (k73_incr_piggyback spH old8 headerPtr headerBytes F))))
      (k73IncreaseStatusFinalPost spH spK (H + 40) gasUsed
        parentPtr Expected (gasLimit >>> 1) headerPtr v9 old18 v19 v20
        parentBytes accWin
        (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)
        (k73_incr_q2 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)
          (gasLimit >>> 1))
        (k73_incr_piggyback spH old8 headerPtr headerBytes F)))
    (hlt : (gasLimit >>> 1).toNat < gasUsed.toNat)
    (htargetPos : 0 < (gasLimit >>> 1).toNat)
    (hleTarget : (gasLimit >>> 1).toNat ≤ 2 ^ 56)
    (hlenP : parentBytes.length = 32)
    (hlenOutWin : outWin.length = 32)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
        (gasUsed - (gasLimit >>> 1)).toNat < 2 ^ 256)
    (hexp : expectedBytes =
      k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) :
    cpsTripleWithin (13 + Nstatus + Ntail) K73 (H + 40) wholeCode
      ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20
        gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes
        (H + 40) old8 (k73_incr_env spK f0 f1 f2 f3 f4 f5 accWin F))
      ((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost spH spK (H + 40) old8 headerPtr
        v9 old18 (gasLimit >>> 1) v19 v20 gasUsed gasLimit parentPtr
        parentBytes headerBytes
        (k73_incr_outj spK parentPtr gasUsed (gasLimit >>> 1) parentBytes
          accWin F)) := by
  subst hexp
  have hpreEq := k73_incr_pre_eq spH spK headerPtr old8 gasLimit gasUsed
    parentPtr v9 old18 v19 v20 parentBytes expectedBytes headerBytes accWin
    f0 f1 f2 f3 f4 f5 F
  have hlenTO : (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin).length = 32 :=
    EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 hlenOutWin
  have hvalA2 : EvmAsm.Crypto.beBytesToNat (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)
      = (EvmAsm.Crypto.beBytesToNat parentBytes *
          ((gasLimit >>> 1) - gasUsed).toNat) % 2 ^ 256 :=
    EvmAsm.Codegen.U256MulU64Be.beBytesToNat_mulOutput parentBytes outWin
      ((gasLimit >>> 1) - gasUsed) hlenP hlenOutWin
  refine cpsTripleWithin_weaken (fun s hp => hpreEq ▸ hp) (fun s hq => ?_) hbranch
  by_cases hpz : EvmAsm.Crypto.beBytesToNat (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) = 0
  · -- replace case: the double-quot window is zero, the clamp fires
    have hcast := k73_incr_machine_bytes_eq_written_replace rfl hlt htargetPos
      hleTarget hlenP hlenTO hMulFit hvalA2 hpz
    rcases hq with hc | hf | hs
    · have hM := k73_incr_carry_routeB_fail spH spK old8 headerPtr parentPtr
        v9 old18 v19 v20 gasUsed (gasLimit >>> 1) parentBytes accWin ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin))
        expectedBytes F s hc
      have hMu := k73_incr_arm_unify spH spK headerPtr parentPtr v9 old18 v19
        v20 gasUsed gasUsed (gasLimit >>> 1) parentBytes accWin outWin
        expectedBytes F hM
      obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hMu
      exact ⟨sa, sb, had, hud, hx1, Or.inr harm⟩
    · exact k73_incr_first_routeB spH spK old8 headerPtr parentPtr v9 old18
        v19 v20 gasUsed (gasLimit >>> 1) parentBytes accWin
        (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1))
        expectedBytes F hcast s hf
    · exact k73_incr_second_routeB spH spK old8 headerPtr parentPtr v9 old18
        v19 v20 gasUsed (gasLimit >>> 1) parentBytes accWin
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) expectedBytes F hcast s hs
  · -- keep case: the double-quot window is nonzero, the clamp is invisible
    have hpNZ : EvmAsm.Crypto.beBytesToNat (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) ≠ 0 := hpz
    have hcast := k73_incr_machine_bytes_eq_written_keep rfl hlt htargetPos
      hleTarget hlenP hlenTO hMulFit hvalA2 hpNZ
    rcases hq with hc | hf | hs
    · have hM := k73_incr_carry_routeB_fail spH spK old8 headerPtr parentPtr
        v9 old18 v19 v20 gasUsed (gasLimit >>> 1) parentBytes accWin ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin))
        expectedBytes F s hc
      have hMu := k73_incr_arm_unify spH spK headerPtr parentPtr v9 old18 v19
        v20 gasUsed gasUsed (gasLimit >>> 1) parentBytes accWin outWin
        expectedBytes F hM
      obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hMu
      exact ⟨sa, sb, had, hud, hx1, Or.inr harm⟩
    · exact k73_incr_first_routeB spH spK old8 headerPtr parentPtr v9 old18
        v19 v20 gasUsed (gasLimit >>> 1) parentBytes accWin
        (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1))
        expectedBytes F hcast s hf
    · exact k73_incr_second_routeB spH spK old8 headerPtr parentPtr v9 old18
        v19 v20 gasUsed (gasLimit >>> 1) parentBytes accWin
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) expectedBytes F hcast s hs

set_option maxRecDepth 8000 in
/-- Wrapper-vocabulary Route-B adapter for the increase arm: the whole
    increase route (mul, two divides, zero test with clamp, add, return)
    discharged of its symmetric multiply-callee premise, stated directly in
    the `k73PreRest` / `k73RouteBCallPost` contract of
    `header_validate_base_fee_spec_within`.  The route's output window is
    threaded as the computed multiply image.  The symmetric multiply-callee
    premise stays EXPLICIT: the pure respeller cannot consume
    `mulWhole_spec` for symbolically-threaded lists (class-b finding on
    issue 12346, WholeRoutes:1085 + WholeSpec:396; k3 prototype precedent) —
    a concrete witness discharges it from `mulWhole_spec` directly, and an
    increase-side native asymmetric contract (mirroring PR #12978) is the
    follow-up bead.  `htargetPos` is the honest static entry condition for
    the divisor (issue 12951); it is never discharged from the emitted code. -/
theorem k73_incr_route_adapter {cr : CodeReq}
    (spH spK old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes accWin outWin : List (BitVec 8))
    (f0 f1 f2 f3 f4 f5 : Word) (F : Assertion)
    (Nstatus Ntail : Nat)
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hne : gasUsed ≠ gasLimit >>> 1)
    (hlt : (gasLimit >>> 1).toNat < gasUsed.toNat)
    (hret : ((H + 40 : Word) &&& ~~~(1 : Word)) = H + 40)
    (hF : F.pcFree)
    (htargetPos : 0 < (gasLimit >>> 1).toNat)
    (hleTarget : (gasLimit >>> 1).toNat ≤ 2 ^ 56)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
        ((gasLimit >>> 1) - gasUsed).toNat < 2 ^ 256)
    (hlenP : parentBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (hlenOutWin : outWin.length = 32)
    (hexp : expectedBytes =
      k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)
    (halignA : parentPtr.toNat % 8 = 0)
    (hoverA : parentPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 → isValidByteAccess
        (parentPtr + BitVec.ofNat 64 j) = true)
    (halignOut : Expected.toNat % 8 = 0)
    (hoverOut : Expected.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 → isValidByteAccess
        (Expected + BitVec.ofNat 64 j) = true)
    (hdisj : parentPtr.toNat + 32 ≤ Expected.toNat ∨
        Expected.toNat + 32 ≤ parentPtr.toNat)
    (hrw : RwRegion.wf ⟨Expected, 32⟩)
    (hroBase : Region.wf ⟨parentPtr, parentBytes⟩)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spK parentPtr Expected (gasLimit >>> 1) gasUsed
        f0 f1 f2 f3 f4 f5 parentBytes accWin ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin))
        (regOwns [.x14, .x15, .x16, .x17] ** k73_incr_piggyback spH old8 headerPtr headerBytes F))
      (k73IncreaseMulCalleePost spK parentPtr Expected (gasLimit >>> 1) gasUsed
        parentBytes accWin ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin))
        (regOwns [.x14, .x15, .x16, .x17] ** k73_incr_piggyback spH old8 headerPtr headerBytes F)))
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn Expected (gasLimit >>> 1) ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin))).body.size + 1) ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn Expected 8 (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1))).body.size + 1) ≤ 2 ^ 64)
    (hszAddQ2 : k73AddBSize parentPtr Expected parentBytes (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) ≤ 2 ^ 64)
    (hszAddOne : k73AddBSize parentPtr Expected parentBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ 2 ^ 64)
    (hNstatus : Nstatus = 3857 + (10 +
        (u256DivU64BeInPlaceFn Expected (gasLimit >>> 1) ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin))).body.steps +
        (u256DivU64BeInPlaceFn Expected 8 (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1))).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) Expected (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1))).body.steps + 1)) + 1)))))
    (hNq2 : 1 + k73AddBTailSteps parentPtr Expected parentBytes (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) ≤ Ntail)
    (hNq1 : 1 + k73AddBTailSteps parentPtr Expected parentBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ Ntail)
    (hNcarry : 9 ≤ Ntail)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i) :
    cpsTripleWithin (13 + Nstatus + Ntail) K73 (H + 40) cr
      ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes (H + 40) old8 (k73_incr_env spK f0 f1 f2 f3 f4 f5 accWin F))
      ((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed gasLimit parentPtr parentBytes headerBytes (k73_incr_outj spK parentPtr gasUsed (gasLimit >>> 1) parentBytes accWin F)) := by
  have hGenv : (k73_incr_piggyback spH old8 headerPtr headerBytes F).pcFree := by
    dsimp only [k73_incr_piggyback]
    pcf
    exact hF
  have ht2 : (gasLimit >>> 1).toNat = gasLimit.toNat / 2 := rfl
  have hsp' : spK + signExtend12 (56 : BitVec 12) = spH := by
    have hx : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
    have hy : signExtend12 (-56 : BitVec 12) =
        (18446744073709551560 : Word) := by decide
    rw [hspK, hx, hy]
    bv_omega
  have hlenTO : (((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin))).length = 32 :=
    EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 hlenOutWin
  have hvalA2 : EvmAsm.Crypto.beBytesToNat (((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)))
      = (EvmAsm.Crypto.beBytesToNat parentBytes *
          ((gasLimit >>> 1) - gasUsed).toNat) % 2 ^ 256 :=
    EvmAsm.Codegen.U256MulU64Be.beBytesToNat_mulOutput parentBytes outWin
      ((gasLimit >>> 1) - gasUsed) hlenP hlenOutWin
  have hq1' : (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) = k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1) := rfl
  have hlen1 : (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)).length = 32 := by
    rw [k73_incr_q1]
    have hq := k73_quot_bytes_natToBytesBE ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)) ((k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)) (gasLimit >>> 1)
      hlenTO hlenTO htargetPos hleTarget
    rw [hq]
    simp
  have hlen2 : (u256DivU64BeQuotBytes (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) 8).length = 32 := by
    have hq := k73_quot_bytes_natToBytesBE (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1)) 8
      hlen1 hlen1 (by decide) (by decide)
    rw [hq]
    simp
  have hretm : ((K73 + 88 : Word) &&& ~~~(1 : Word)) = K73 + 88 :=
    EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
  have hret1 : ((K73 + 104 : Word) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4 := by
    decide
  have hret2 : ((K73 + 120 : Word) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4 := by
    decide
  have hcallRet : ((K73 + 188 : Word) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4 := by
    decide
  have hsaved : (k73Saved (H + 40) headerPtr v9 old18 v19 v20) .x1 = H + 40 := rfl
  have hwTri := k73_incr_hw_triple spH spK (H + 40) gasLimit gasUsed (gasLimit >>> 1) parentPtr Expected
    headerPtr v9 old18 v19 v20 f0 f1 f2 f3 f4 f5 parentBytes accWin (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin)
    (k73_incr_q1 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1))
    (k73_incr_q2 (k73_incr_outT parentBytes ((gasLimit >>> 1) - gasUsed) outWin) (gasLimit >>> 1))
    (k73_incr_piggyback spH old8 headerPtr headerBytes F) Nstatus Ntail
    hGenv hsp' rfl hne hlt hret hsaved hcallee hrw hlenTO rfl rfl hlen1 hlen2
    hoverOut htargetPos hsz1 hsz2 hret1 hret2 hroBase hlenP hoverA hdisj
    hszAddQ2 hszAddOne hcallRet hNstatus hNq2 hNq1 hNcarry
  exact cpsTripleWithin_extend_code hk73Mono
    (k73_incr_funnel_close spH spK old8 headerPtr parentPtr gasLimit gasUsed
      v9 old18 v19 v20 f0 f1 f2 f3 f4 f5 parentBytes expectedBytes headerBytes
      accWin outWin F Nstatus Ntail hwTri hlt htargetPos hleTarget hlenP
      hlenOutWin hMulFit hexp)


end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute
