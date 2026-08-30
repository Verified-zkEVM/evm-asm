/-
  #12850: the taylor-layer tie for the linked exponential.

  The linked image has NO separate `taylor_exponential` symbol: the reference
  recurrence `taylor_exponential(1, excess_blob_gas, 11684671)` is inlined as
  the loop nest of `amsterdam_blob_gas_price_u256`
  (`GuestAddrs.amsterdam_blob_gas_price_u256`, `amsterdamBlobGasPriceU256_prog`,
  252 instructions).  This file pins the taylor-layer vocabulary that the
  whole-routine contract for that routine must satisfy:

  * `natToBeBytes` — the 32-byte big-endian encoding the routine's status-0
    exit writes through the output pointer (the epilogue stores
    `out[k] = sum_byte[31 - k]`, i.e. big-endian);
  * `priceOutcome` — the model-determined outcome (status + exact output
    bytes) computed from `taylorExp384`;
  * `taylorPriceContract` — the model-determined whole-routine contract: a
    single-exit `cpsTripleWithin` per outcome (the model FIXES which exit the
    run takes, so this is not an N-branch).  Discharging it is the open seam —
    item 7 of the K70 inventory in
    `HeaderValidateExcessBlobGasSpec.lean`, and the machine work of #12851.

  Kernel calibration proved here:
  * the degenerate inhabitant's outcome: `taylorExp384 0 = some 1`
    (one-step trace proof; pairs with the existing concrete entry-state
    witness `priceEntryRest_inhabited`, whose layout uses excess = 0);
  * the discriminating pair: outcome status 0 at `10 * taylorDenominator`
    versus status 1 at the measured overflow boundary `2,073,394,371`
    (`taylorModelResult_boundary_none`).
-/
import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Stateless.SpecRef.TaylorExponential

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorTie

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceU256Sat
open EvmAsm.Stateless.SpecRef

/-! ## Output encoding

`natToBeBytes len r` is the `len`-byte big-endian encoding of `r`, truncated
to the low `len` bytes by the shifts.  For the status-0 exit the routine
writes exactly `natToBeBytes 32 r` at the output pointer when the model
result is `r` (high limbs of the Taylor sum are checked to be zero first, so
`r < 2^256` on that path). -/

def natToBeBytes (len r : Nat) : List (BitVec 8) :=
  (List.range len).map (fun k => BitVec.ofNat 8 ((r >>> (8 * (len - 1 - k))) % 256))

theorem natToBeBytes_length (len r : Nat) :
    (natToBeBytes len r).length = len := by
  simp [natToBeBytes, List.length_map, List.length_range]

/-! ## Model-determined outcome -/

/-- The routine's (status, output bytes) pair as determined by the exact
bounded model: status 0 with the 32-byte BE encoding of the result on
`some`, status 1 (output left unspecified — `priceOutputPost` then keeps
only ownership of the four output dwords) on `none`. -/
def priceOutcome (excess : Nat) : Word × List (BitVec 8) :=
  match taylorExp384 excess with
  | some r => (0, natToBeBytes 32 r)
  | none => (1, [])

/-- The taylor-layer whole-routine contract: the linked routine at
`PriceK` over `priceCode` satisfies the model-determined exit of
`priceOutcome excess.toNat`.  The numeric envelope enters as the explicit
precondition family carried by `taylorExp384`'s own characterization
(`excess.toNat < 2^64` for the input register; acceptance is exactly
`taylorExpNat 1 excess.toNat taylorDenominator < 2^256`), plus the machine's
measured sizing constants (loop cap `i < 496` covering the 495 measured
transitions; in-envelope boundary peak 306 bits, full-domain pre-division
product peak 377 bits — sizing facts of the emitted loop nest, recorded in
`Header.lean`'s routine docstring).

DISCHARGE STATUS: open.  This is the seam premise that K70
(`k70_abi_from_body` / `priceContract`) and #12851 consume; proving it
requires the loop-nest Hoare triple for the 252-instruction routine.  It is
stated here so the seam has one canonical model-tied shape instead of a
proof-convenient weakening.  The public contract preserves one caller
residual assertion on both sides; `taylorPriceContractCore` is its
machine-owned `empAssertion` form and `taylorPriceContract_frame` supplies
the general PC-free frame. -/
def taylorPriceContractCore (n : Nat) (sp0 ret : Word) (vals : Reg → Word)
    (excess outPtr : Word) : Prop :=
  cpsTripleWithin n PriceK ret priceCode
    (priceEntryRest sp0 ret vals excess outPtr empAssertion)
    (priceCalleePost sp0 ret vals (priceOutcome excess.toNat).1 outPtr
      (priceOutcome excess.toNat).2 empAssertion)

def taylorPriceContract (n : Nat) (sp0 ret : Word) (vals : Reg → Word)
    (excess outPtr : Word) (scratch : Assertion) : Prop :=
  cpsTripleWithin n PriceK ret priceCode
    (priceEntryRest sp0 ret vals excess outPtr scratch)
    (priceCalleePost sp0 ret vals (priceOutcome excess.toNat).1 outPtr
      (priceOutcome excess.toNat).2 scratch)

/-- Carry a caller-owned, PC-free residual through the model-indexed
    whole-routine contract.  This is the same frame step as the body and K70
    N-branch forms; the machine-owned core is proved once against `empAssertion`.
-/
theorem taylorPriceContract_frame
    {n : Nat} (sp0 ret : Word) (vals : Reg → Word)
    (excess outPtr : Word) (scratch : Assertion)
    (hcore : taylorPriceContractCore n sp0 ret vals excess outPtr)
    (hscratch : scratch.pcFree) :
    taylorPriceContract n sp0 ret vals excess outPtr scratch := by
  unfold taylorPriceContract
  unfold taylorPriceContractCore at hcore
  have hfr := cpsTripleWithin_frameR scratch hscratch hcore
  simpa only [priceEntryRest, priceCalleePost, priceCalleePostCore,
    sepConj_emp_right', sepConj_emp_left', sepConj_assoc'] using hfr

/-! ## Kernel calibration -/

/-- The degenerate inhabitant's model outcome: excess = 0 accepts with
result 1 (`e^0`), by a one-step trace — the Taylor constant drives one
recurrence transition before the accumulator reaches zero.  Together with
`priceEntryRest_inhabited` (whose concrete layout uses excess = 0) this
calibrates the status-0 side of `priceOutcome` at the kernel level. -/
theorem taylor_price_outcome_zero : taylorExp384 0 = some 1 := by
  have h_trace :
      taylorTraceValidTo 0 taylorDenominator taylorInitial
        [{ i := 2, acc := 0, output := taylorDenominator }] := by
    simp only [taylorTraceValidTo, taylorTraceStep, taylorInitial]
    norm_num [taylorDenominator]
  have h_aux :
      taylorNatAux 0 taylorDenominator 1 taylorDenominator 0 =
        taylorDenominator := by
    have h := taylorNatAux_eq_trace 0 taylorDenominator taylorInitial
      [{ i := 2, acc := 0, output := taylorDenominator }] h_trace
    simpa [taylorTraceFinal, taylorInitial] using h
  have h_result : taylorExpNat 1 0 taylorDenominator = 1 := by
    unfold taylorExpNat
    simp only [Nat.one_mul]
    rw [h_aux]
    exact Nat.div_self (by decide)
  have h_lt : taylorExpNat 1 0 taylorDenominator < taylorResultBound := by
    rw [h_result]
    decide
  rw [taylorExp384_some_of_lt 0 (by decide) h_lt, h_result]

/-- Kernel-level discrimination of the two exits: `10 * taylorDenominator`
accepts (status 0) while the measured overflow boundary `2,073,394,371`
rejects (status 1).  The pair witnesses that `priceOutcome` is not a
constant shape — the contract's exit genuinely depends on the input. -/
theorem taylor_price_outcomes_discriminate :
    (priceOutcome (10 * taylorDenominator)).1 = 0 ∧
      (priceOutcome 2073394371).1 = 1 := by
  constructor
  · have h10 : taylorModelResult (10 * taylorDenominator) =
      some (taylorExpNat 1 (10 * taylorDenominator) taylorDenominator) :=
      taylorModelResult_10D
    simp only [priceOutcome]
    rw [show taylorExp384 (10 * taylorDenominator) =
      some (taylorExpNat 1 (10 * taylorDenominator) taylorDenominator) from by
        simpa [taylorModelResult] using h10]
  · simp only [priceOutcome]
    rw [show taylorExp384 2073394371 = none from taylorModelResult_boundary_none]

/-- The status-0 output bytes have the advertised length at the degenerate
inhabitant's outcome (`natToBeBytes 32 1`). -/
theorem taylor_price_outcome_zero_bytes_length :
    (priceOutcome 0).2.length = 32 := by
  simp only [priceOutcome]
  rw [taylor_price_outcome_zero]
  exact natToBeBytes_length 32 1

/-- Re-export of the concrete non-degenerate entry layout for the
taylor-layer contract: `priceEntryRest` at the Amsterdam sample geometry
(excess = 0) is satisfiable at a real machine state.  This is the
inhabitant side of the non-vacuity pair; the discriminating side is
`taylor_price_outcomes_discriminate`. -/
theorem taylor_price_entry_inhabited :
    (priceEntryRest sampleSp0 sampleRet sampleSaved
      (0 : Word) sampleOutPtr priceScratch).holdsFor sampleState :=
  priceEntryRest_inhabited

#print axioms taylorPriceContract_frame
#print axioms taylor_price_outcome_zero
#print axioms taylor_price_outcomes_discriminate
#print axioms taylor_price_outcome_zero_bytes_length
#print axioms taylor_price_entry_inhabited

end EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorTie
