/-
  EvmAsm.Codegen.Proofs.WitnessCodeLookupSpec

  Verified triples for the `wcidx_*` code-index helpers
  (`Programs/WitnessCodeLookup.lean`), by transfer: `wcidx_cmp32` and
  `wcidx_swap_records` are token-for-token clones of the already-verified
  `widx_cmp32` / `widx_swap_records` (`Proofs/MptWitnessIndexSpec.lean`),
  so their universally-quantified-base specs instantiate directly — the
  program equality is definitional.

  Progress toward DRIFT obligation 10 ("no `cpsTripleWithin` for the
  code-DB routines"): the compare helper of `witness_codes_index_build`
  now carries a machine-level triple at every base, including its guest
  placement.

  ⛔ `wcidx_swap_records` does NOT get a transferred triple from this
  path: the previously proved `widxSwapProg` is a register-allocation
  VARIANT of the deployed program (`x6` vs `x31` loop counter) —
  `wcidxSwapRecords_prog ≠ widxSwapProg` is decide-checkable below.
  The DEPLOYED register allocation is instead proved directly (and
  unified over the equal-pointer case) by the proof-first port in
  `Programs/WcidxSwapRecordsSAsm.lean` (`wsrFn_spec`).
-/

import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Codegen.Programs.WitnessCodeLookup

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64

/-- `Program` is a def alias, opaque to instance search. -/
local instance : DecidableEq Program :=
  inferInstanceAs (DecidableEq (List Instr))

/-- The code-index compare program is the witness-index compare program,
    token for token. -/
theorem wcidxCmp32_prog_eq :
    wcidxCmp32_prog = widxCmp32Prog := rfl

/-- The deployed code-index swap IS the (reconciled, #12990) proved swap
    program: after `widxSwapProg` was transposed onto the image's
    `x31`-counter register allocation, the two clones coincide, so
    `widx_swap_records_spec` now TRANSFERS to the code-index copy at any
    base (previously a ⛔ negative control, `wcidxSwapRecords_prog_ne`).
    The clone's own DCode proof in `Programs/WcidxSwapRecordsSAsm.lean`
    is unaffected. -/
theorem wcidxSwapRecords_prog_eq :
    wcidxSwapRecords_prog = widxSwapProg := by decide

/-- `wcidx_cmp32`: 32-byte unsigned compare over code-index hashes —
    the `widx_cmp32` triple, transferred to the clone at any base. -/
theorem wcidx_cmp32_spec
    (base ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64)
    (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 293 base ret
      (CodeReq.ofProg base wcidxCmp32_prog)
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as **
       bytesRegion ptrB bs)
      (widxCmp32Post ptrA ptrB ret as bs) := by
  rw [wcidxCmp32_prog_eq]
  exact widx_cmp32_spec base ret ptrA ptrB as bs hlenA hlenB
    halignA halignB hovA hovB hvalidA hvalidB halignRet

/-- **`wcidx_cmp32`, whole-routine flat triple at the guest entry** — the
    image claim, obtained from `wcidx_cmp32_spec` by instantiating its free
    `base` at `GuestAddrs.wcidx_cmp32` (the spec is already stated over the
    image's `wcidxCmp32_prog`, per its `GuestImageEntries` pairing; no
    program identity rewrite needed).

    Domain: both buffers 32 bytes, both bases 8-ALIGNED, non-overflowing,
    `isValidByteAccess` over both windows — real restrictions, so this is
    not total over its argument types. -/
theorem wcidxCmp32Entry_spec
    (ret ptrA ptrB : Word) (as bs : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : ptrA.toNat % 8 = 0) (halignB : ptrB.toNat % 8 = 0)
    (hovA : ptrA.toNat + 32 < 2 ^ 64)
    (hovB : ptrB.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 →
      isValidByteAccess (ptrA + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 →
      isValidByteAccess (ptrB + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 293 (BitVec.ofNat 64 GuestAddrs.wcidx_cmp32) ret
      (CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.wcidx_cmp32)
        wcidxCmp32_prog)
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as **
       bytesRegion ptrB bs)
      (widxCmp32Post ptrA ptrB ret as bs) :=
  wcidx_cmp32_spec (BitVec.ofNat 64 GuestAddrs.wcidx_cmp32) ret ptrA ptrB
    as bs hlenA hlenB halignA halignB hovA hovB hvalidA hvalidB halignRet

end EvmAsm.Codegen.Proofs
