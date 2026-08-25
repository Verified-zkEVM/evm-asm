/-
  EvmAsm.Evm64.Accelerators.Dispatch

  Skeletal ECALL dispatch hook for the cryptographic accelerators declared in
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`.

  This module provides a thin dispatch surface that maps an incoming ECALL
  selector (the value in `x5` / `t0`) to a per-accelerator placeholder handler
  returning `ZkvmStatus.efail` (not-implemented). Concrete per-accelerator
  bridges land in subsequent slices (KECCAK, SHA256/RIPEMD160/BLAKE2F,
  secp256k1, MODEXP/BN254/BLS12/KZG, secp256r1).

  Design notes:

  * The dispatch is a separate, pure `Nat → ZkvmStatus` function that does
    not overlap with the active ECALL handlers in `execInstrBr`. Active
    handlers: `HALT` (0x00), `write_output` (0x10), `read_input` (0xF2).
    Note: `HINT_LEN` (0xF0) and `HINT_READ` (0xF1) have been retired;
    their handler branches and specs were removed from `Execution.lean` and
    `HintSpecs.lean`.

  * `isAccelerator` distinguishes accelerator selectors (the 19 IDs from
    `EvmAsm/Evm64/Accelerators/SyscallIds.lean`) from the framing selectors
    (HALT/COMMIT/HINT_LEN/HINT_READ — the latter two are deprecated but
    retained as named constants for disjointness proofs). It is decidable so
    later slices can `decide` membership and `cases` on it.

  * `dispatch` returns `.efail` everywhere for now. As each concrete bridge
    lands, the corresponding branch will be replaced with a payload-aware
    handler producing `.eok` on the happy path; the structural framework
    (selector → status) does not change.

  Refs: parent beads task `evm-asm-nr2sk`, slice `evm-asm-xofw2`.
-/

module

public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm
namespace Accelerators

open SyscallId

/-- The 19 accelerator selector IDs declared in `SyscallIds.lean`. The list
is canonical: any future per-function bridge should case on it via
`acceleratorSelectors.mem` rather than re-listing the IDs locally. -/
def acceleratorSelectors : List Nat :=
  [keccak256, secp256k1_verify,
   secp256k1_ecrecover, sha256, ripemd160, modexp,
   bn254_g1_add, bn254_g1_mul, bn254_pairing,
   blake2f, kzg_point_eval,
   bls12_g1_add, bls12_g1_msm, bls12_g2_add, bls12_g2_msm,
   bls12_pairing, bls12_map_fp_to_g1, bls12_map_fp2_to_g2,
   secp256r1_verify]

/-- The canonical accelerator selector table contains exactly 19 entries. -/
theorem acceleratorSelectors_length :
    acceleratorSelectors.length = 19 := by
  decide

/-- The canonical accelerator selector table has no duplicate IDs. -/
theorem acceleratorSelectors_nodup :
    acceleratorSelectors.Nodup := by
  decide

/-- Decidable predicate: `id` is one of the accelerator selectors. -/
def isAccelerator (id : Nat) : Prop := id ∈ acceleratorSelectors

instance (id : Nat) : Decidable (isAccelerator id) :=
  inferInstanceAs (Decidable (id ∈ acceleratorSelectors))

/-- Skeletal ECALL dispatch: every accelerator selector maps to
`ZkvmStatus.efail` (not-yet-implemented). Non-accelerator selectors also
map to `.efail`; handler routing for the framing selectors lives in
`EvmAsm/Rv64/Execution.lean` and is intentionally unchanged.

Subsequent slices replace individual branches with payload-aware handlers
that may return `.eok` on the happy path; this signature is the contract
those bridges will satisfy. -/
def dispatch (_id : Nat) : ZkvmStatus := ZkvmStatus.efail

@[simp] theorem dispatch_eq_efail (id : Nat) :
    dispatch id = ZkvmStatus.efail := rfl

@[simp] theorem dispatch_isOk_false (id : Nat) :
    (dispatch id).isOk = false := rfl

/-- RV64 `a0` return-register encoding for the skeletal accelerator dispatch. -/
def dispatchWord (id : Nat) : BitVec 64 :=
  Rv64.zkvmStatusToWord (dispatch id)

@[simp] theorem dispatchWord_eq_efailWord (id : Nat) :
    dispatchWord id = Rv64.zkvmStatusEfailWord := rfl

theorem dispatchWord_ne_eokWord (id : Nat) :
    dispatchWord id ≠ Rv64.zkvmStatusEokWord := by
  rw [dispatchWord_eq_efailWord]
  exact Rv64.zkvmStatusEokWord_ne_efailWord.symm

theorem dispatchWord_decodes_efail (id : Nat) :
    Rv64.zkvmStatusFromWord? (dispatchWord id) = some ZkvmStatus.efail := by
  simp [dispatchWord]

/-! ## Sanity properties

These confirm the framing/accelerator partition without forcing any
concrete numeric values into client proofs. -/

/-- HALT is not an accelerator selector. -/
theorem not_isAccelerator_halt : ¬ isAccelerator halt := by decide

/-- COMMIT is not an accelerator selector. -/
theorem not_isAccelerator_commit : ¬ isAccelerator commit := by decide

/-- HINT_LEN is not an accelerator selector. -/
theorem not_isAccelerator_hintLen : ¬ isAccelerator hintLen := by decide

/-- HINT_READ is not an accelerator selector. -/
theorem not_isAccelerator_hintRead : ¬ isAccelerator hintRead := by decide

/-- Each declared accelerator ID is recognised by `isAccelerator`. -/
theorem isAccelerator_keccak256 : isAccelerator keccak256 := by decide
theorem isAccelerator_secp256k1_verify : isAccelerator secp256k1_verify := by decide
theorem isAccelerator_secp256k1_ecrecover : isAccelerator secp256k1_ecrecover := by decide
theorem isAccelerator_sha256 : isAccelerator sha256 := by decide
theorem isAccelerator_ripemd160 : isAccelerator ripemd160 := by decide
theorem isAccelerator_modexp : isAccelerator modexp := by decide
theorem isAccelerator_bn254_g1_add : isAccelerator bn254_g1_add := by decide
theorem isAccelerator_bn254_g1_mul : isAccelerator bn254_g1_mul := by decide
theorem isAccelerator_bn254_pairing : isAccelerator bn254_pairing := by decide
theorem isAccelerator_blake2f : isAccelerator blake2f := by decide
theorem isAccelerator_kzg_point_eval : isAccelerator kzg_point_eval := by decide
theorem isAccelerator_bls12_g1_add : isAccelerator bls12_g1_add := by decide
theorem isAccelerator_bls12_g1_msm : isAccelerator bls12_g1_msm := by decide
theorem isAccelerator_bls12_g2_add : isAccelerator bls12_g2_add := by decide
theorem isAccelerator_bls12_g2_msm : isAccelerator bls12_g2_msm := by decide
theorem isAccelerator_bls12_pairing : isAccelerator bls12_pairing := by decide
theorem isAccelerator_bls12_map_fp_to_g1 : isAccelerator bls12_map_fp_to_g1 := by decide
theorem isAccelerator_bls12_map_fp2_to_g2 : isAccelerator bls12_map_fp2_to_g2 := by decide
theorem isAccelerator_secp256r1_verify : isAccelerator secp256r1_verify := by decide

end Accelerators
end EvmAsm
