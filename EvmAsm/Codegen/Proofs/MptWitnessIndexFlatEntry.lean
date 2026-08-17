/-
  EvmAsm.Codegen.Proofs.MptWitnessIndexFlatEntry

  Guest-address instantiations of two `MptWitnessIndexSpec` triples, so they become
  the `GuestImageEntries` image claim and are rowable (#12244).

  ## What was missing

  `widx_cmp32_spec` and `widx_record_ptr_spec` are already flat whole-routine
  `cpsTripleWithin`s — but at a FREE `base`, over a `CodeReq.ofProg base <prog>` whose
  program is the module's own `widxCmp32Prog` / `widxRecordPtrProg hi lo` rather than
  the image's `widxCmp32_prog` / `widxRecordPtr_prog`. Position-independence is the
  right way to state them (they are reusable at any link address), but as stated
  neither is the claim `GuestImageEntries.lean` makes, so neither was rowable.

  ⚠️ Note this is a THIRD distinct blocker, different from the two the
  registry-coverage allowlist knows about. It is not "needs `Fn.retSpecFlat`" (there is
  no `Fn` here at all, and no structured spec), and it is not a union `CodeReq`. It is:
  *flat, whole-routine, but position-independent* — closed by instantiating `base` and
  identifying the program.

  ## What closes it

  Two kernel-checked program identities, and nothing else:

  * `widxCmp32Prog = widxCmp32_prog` — by `decide`; the two definitions agree
    instruction for instruction.
  * `widxRecordPtrProg (laHi …) (laLo …) = widxRecordPtr_prog` — by `rfl`, NOT `decide`:
    Lean cannot synthesize `Decidable` for this equation through `laHi`/`laLo`, and the
    identity is definitional anyway. The proved body takes
    the `auipc`/`addi` immediates as PARAMETERS precisely because the `widx_records`
    data label is link-layout dependent; supplying the image's own `laHi`/`laLo` for
    `widx_records` relative to `widx_record_ptr + 12` is what pins them.

  ⛔ **`widx_swap_records` is deliberately NOT here.** Its `widxSwapProg` and the
  image's `widxSwapRecords_prog` are DIFFERENT programs — the proved variant uses `x6`
  as the loop counter where the image uses `x31` — and `widxSwapProg ≠
  widxSwapRecords_prog` is `decide`-checkable. So that triple is about a variant of the
  routine, not the linked code, and instantiating its base would NOT make it the image
  claim. Rowing it would be an overclaim; it stays unrowed with that reason recorded.
-/

import EvmAsm.Codegen.Proofs.MptWitnessIndexSpec
import EvmAsm.Codegen.Programs.MptWitnessIndex

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

/-! ## The two program identities, kernel-checked -/

/-- The proved `widx_cmp32` program IS the image's. -/
theorem widxCmp32Prog_eq : widxCmp32Prog = widxCmp32_prog := by decide

/-- The proved `widx_record_ptr` program is the image's once its two link-dependent
    immediates are supplied from the image's own relocation. -/
theorem widxRecordPtrProg_eq :
    widxRecordPtrProg
        (laHi GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12))
        (laLo GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12))
      = widxRecordPtr_prog := by
  -- ⚠️ NOT `decide`: Lean cannot synthesize `Decidable` for this equation through
  -- `laHi`/`laLo`. The identity is definitional — the image program literally IS the
  -- parameterised body at those immediates — so `rfl` is the right (and cheaper) tool.
  rfl

/-- ⛔ Negative control for the module header's claim: the swap routine's proved
    program is NOT the image's, so no instantiation makes that triple the image claim.
    Kept as a theorem so the claim cannot rot silently — if the two are ever
    reconciled, this fails and the note above must be revisited. -/
theorem widxSwapProg_ne : widxSwapProg ≠ widxSwapRecords_prog := by decide

/-! ## The rowable entry triples -/

/-- **`widx_cmp32`, whole-routine flat triple at the guest entry.**

    Byte-compares the two 32-byte buffers at `a0`/`a1` and returns a three-way verdict
    in `a0`: `1` if equal, `0` if `as < bs`, `2` otherwise (big-endian lexicographic
    order IS numeric order). Both input regions are pinned INTACT.

    Anchored over `CodeReq.ofProg (GuestAddrs.widx_cmp32) widxCmp32_prog`, exactly the
    `GuestImageEntries` pairing, so this IS the image claim and is rowable. Obtained
    from `widx_cmp32_spec` by instantiating its free `base` and rewriting with
    `widxCmp32Prog_eq`; no new proof content.

    Domain: both buffers 32 bytes, both bases 8-ALIGNED, non-overflowing, and
    `isValidByteAccess` over both windows — real restrictions, so this is not total
    over its argument types. -/
theorem widxCmp32Entry_spec
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
    cpsTripleWithin 293 (GuestAddrs.widx_cmp32 : Word) ret
      (CodeReq.ofProg (GuestAddrs.widx_cmp32 : Word) widxCmp32_prog)
      (regOwn .x5 ** ((.x10 : Reg) ↦ᵣ ptrA) ** ((.x11 : Reg) ↦ᵣ ptrB) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** bytesRegion ptrA as ** bytesRegion ptrB bs)
      (widxCmp32Post ptrA ptrB ret as bs) := by
  have h := widx_cmp32_spec (GuestAddrs.widx_cmp32 : Word) ret ptrA ptrB as bs
    hlenA hlenB halignA halignB hovA hovB hvalidA hvalidB halignRet
  rwa [widxCmp32Prog_eq] at h

/-- **`widx_record_ptr`, whole-routine flat triple at the guest entry.**

    Computes `widx_records + 48 * a0` into `a0` (via `a0<<<5 + a0<<<4`), clobbering
    `t0`/`t1`; every other exposed register is preserved, and the post is the explicit
    register-file transformer `widxRecordPtrResult`, i.e. a COMPLETE deterministic
    description of the routine's effect. Pure register arithmetic — no memory
    footprint.

    Anchored over `CodeReq.ofProg (GuestAddrs.widx_record_ptr) widxRecordPtr_prog`, the
    `GuestImageEntries` pairing. Obtained from `widx_record_ptr_spec` by instantiating
    its free `base` AND its two link-dependent immediates with the image's own
    `laHi`/`laLo` for `widx_records`, then rewriting with `widxRecordPtrProg_eq`.

    ⭐ TOTAL over its argument types: the only hypothesis is an aligned return address.
    ⚠️ But note the post is stated via `widxRecordPtrResult base hi lo rf`, which still
    mentions the concrete `hi`/`lo`; a spec-level reader wanting "= widx_records +
    48 * i" has to unfold that transformer. -/
theorem widxRecordPtrEntry_spec (ret : Word) (rf : RegFile)
    (halign : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin 7 (GuestAddrs.widx_record_ptr : Word) ret
      (CodeReq.ofProg (GuestAddrs.widx_record_ptr : Word) widxRecordPtr_prog)
      (regAtoms rf exposedRegs ** (.x1 ↦ᵣ ret))
      (regAtoms
        (widxRecordPtrResult (GuestAddrs.widx_record_ptr : Word)
          (laHi GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12))
          (laLo GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)) rf)
        exposedRegs ** (.x1 ↦ᵣ ret)) := by
  have h := widx_record_ptr_spec (GuestAddrs.widx_record_ptr : Word) ret
    (laHi GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12))
    (laLo GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)) rf halign
  rwa [widxRecordPtrProg_eq] at h

end EvmAsm.Codegen.Proofs
