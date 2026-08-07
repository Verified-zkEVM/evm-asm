/-
  EvmAsm.Codegen.Programs.RequestsHashParams

  The ten SSZ constants `execution_requests_hash` validates against, tied to
  `SpecRef` (GH #11578).

  ## What this fixes

  `RequestsHash.lean:50-59` gates five request bodies on a stride and a cap
  each — `192`/`76`/`116`/`184`/`68` and `8192`/`16`/`2`/`64`/`16`. All ten are
  **bare decimal literals in the emitter, pinned by nothing.** Their only
  documentation is the `vdfs9` comment above them; nothing machine-checked ties
  them to the SSZ types they are supposed to come from, so a container gaining a
  field would leave the guest silently validating against a stale stride.

  Each `#guard` below is `by decide`-cheap — `SszType.fixedSize` is
  kernel-reducible (`SpecRef/SszCodec.lean:76-88`) — and turns folklore into a
  build failure. Same device as
  `#guard beBytesToNat bls12PBytes = 0x1a0111ea…` (`Bls12G1LtPSAsm.lean:85`),
  which is what keeps the BLS prime honest.

  ## ⚠️ The strides are DERIVED, not declared, and that is the point

  There is no `sszDepositRequestFixedSize` constant anywhere; `192` is recoverable
  only by summing `sszDepositRequestType`'s field widths (`SpecRef/Ssz.lean:87-88`:
  `48 + 32 + 8 + 96 + 8`). The caps, by contrast, *are* named
  (`MAX_*_PER_PAYLOAD`, `Ssz.lean:30-34`). So the cap guards check a name against
  a literal while the stride guards check a **computation** against a literal —
  the latter are the ones that would catch a schema change.

  ## Placement

  Codegen-side, in a sibling module rather than in `RequestsHash.lean` itself.
  `check-layering` L1 lets Codegen cite `SpecRef` freely, but `RequestsHash.lean`
  imports only `Rv64.Program` today, and pushing the whole SpecRef SSZ tower onto
  the emitter — which five other emitters concatenate — would be a real rebuild
  cost for a set of `#guard`s.
-/

-- `Ssz.lean` is the one that carries the request container types and the
-- `MAX_*_PER_PAYLOAD` caps, and it imports `SszCodec` (for `SszType.fixedSize`)
-- rather than the other way round — so this single import gets both.
import EvmAsm.Stateless.SpecRef.Ssz
-- The `remu`/`divu` bridges the validation triple discharges its `bnez`/`bgtu`
-- obligations with. Imported here rather than left for the triple's module so
-- the two halves of this routine's vocabulary — its constants and its
-- arithmetic — arrive together.
import EvmAsm.Rv64.RemuNat

namespace EvmAsm.Codegen.RequestsHashParams

open EvmAsm.Stateless.SpecRef

/-! ## Strides — the fixed size of one element of each request list

    These are the `li t1, …` divisors at `RequestsHash.lean:50/52/54/56/58`. -/

#guard SszType.fixedSize sszDepositRequestType == 192
#guard SszType.fixedSize sszWithdrawalRequestType == 76
#guard SszType.fixedSize sszConsolidationRequestType == 116
#guard SszType.fixedSize sszBuilderDepositRequestType == 184
#guard SszType.fixedSize sszBuilderExitRequestType == 68

/-! ## Caps — the `li t3, …` bounds at `RequestsHash.lean:51/53/55/57/59` -/

#guard MAX_DEPOSIT_REQUESTS_PER_PAYLOAD == 8192
#guard MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD == 16
#guard MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD == 2
#guard MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD == 64
#guard MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD == 16

/-! ## The offset table's size — the `20` in three separate guest checks

    `li t0, 20; bltu s1, t0` (length floor, `RequestsHash.lean:25`) and
    `li t0, 20; bne s3, t0` (the `hbo40` exact-equality fix, `:37`) both encode
    the same quantity: the fixed part of `SszExecutionRequests`, which is five
    variable `SszList` fields at one offset each.

    ⭐ This is the guard that would have caught the `hbo40` false-accept class in
    the first place, because it makes the number a consequence of the schema
    rather than a constant someone typed twice. -/

#guard SszType.fixedSize sszExecutionRequestsType == 20
#guard sszOffsetSize * 5 == 20

/-! ## The reference imposes the very checks the guest performs

    ⚠️ Recorded here because #11578 and `docs/leaf-routine-targets.md:115` both
    name `compute_requests_hash` as this routine's counterpart, and that is the
    **wrong anchor**: `compute_requests_hash` (`SpecRef/SeamShell.lean:103`) is
    `sha256 (requests.flatMap sha256)` — total, and imposing neither the
    divisibility nor the caps. It anchors the hashing half, which #11578 splits
    off deliberately.

    The validation half's counterpart is `SszCodec.deserializeAux`'s fixed-size
    list arm (`SpecRef/SszCodec.lean:235-241`), which performs exactly the pair
    the guest does:

    * `data.length % sz != 0` → reject  ↔  `remu t2, t0, t1; bnez t2, .Lerh_fail`
    * `count > lim` → reject            ↔  `divu t2, t0, t1; bgtu t2, t3, .Lerh_fail`

    Same operators, and the same strictness: `>` not `≥`, so `count == cap` is
    **accepted** on both sides. The guest's `bgtu` (not `bgeu`) is therefore not
    an off-by-one but a match.

    The offset checks line up with the container arm at `:201-216`, including
    `varOffsets.getD 0 fixedLen != fixedLen` (`:211`) — which IS the `hbo40`
    exact-equality requirement — and `data.length < fixedLen` (`:203`), which is
    the `bltu s1, 20`.

    The witnesses below pin the two element sizes the reference divides by, so
    "the reference divides by the same number the guest does" is checked rather
    than asserted in this comment. -/

#guard (sszExecutionRequestsType.fixedSize == 20 &&
        SszType.fixedSize sszDepositRequestType == 192)

/-- A stride is never zero, which is the side condition both the reference and
    the guest need: `deserializeAux` rejects `sz = 0` explicitly
    (`SszCodec.lean:237`) and `rv64_remu`/`rv64_divu` have no trap, returning `a`
    and `allOnes` respectively on a zero divisor. Stated as a theorem rather than
    a `#guard` because a triple has to *use* it. -/
theorem request_strides_pos :
    0 < SszType.fixedSize sszDepositRequestType ∧
    0 < SszType.fixedSize sszWithdrawalRequestType ∧
    0 < SszType.fixedSize sszConsolidationRequestType ∧
    0 < SszType.fixedSize sszBuilderDepositRequestType ∧
    0 < SszType.fixedSize sszBuilderExitRequestType := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end EvmAsm.Codegen.RequestsHashParams
