/-
  EvmAsm.Progress.Routines

  Drift-proof registry of **verified guest routines** — the non-opcode half of
  the verified surface (GH #11042).

  ## Why this is a second registry rather than added rows

  `EvmAsm.Progress.registry` is `OpcodeEntry`-shaped: every row is an EVM
  opcode, keyed on the mnemonic, carrying `cycleBound` and opcode-shaped
  fields. A guest routine (`rlp_encode_uint_be`, `rlp_item_size`, the RLP walk
  chain) has no opcode name to key on, so it cannot be a row there. The
  consequence, before this module existed, was that **no guest-routine spec was
  covered by `scripts/check-axioms.sh`** — the kernel-truth gate audits exactly
  what the opcode registry classifies. `rlp_encode_uint_be` is the case that
  surfaced it: the whole-routine triple `reub_spec_within` is the strongest
  claim this repo makes about that routine, and nothing was witnessing it.

  ## Why this lives beside `EvmAsm.Progress` rather than inside it

  Witnessing a guest routine means importing the module that proves it, and
  those live under `EvmAsm.Codegen.Programs.*` (815 modules) — the part of the
  tree with the most churn. `EvmAsm.Progress` is imported by
  `Progress.Correspondence`, `Progress.Obligations` and
  `Progress.AxiomWitnesses`; pulling Codegen into it would make every Codegen
  edit rebuild the opcode gate. Keeping the routine registry in a sibling
  module leaves the opcode side's rebuild cost unchanged. `ProofTier` is shared
  (imported), so the two registries stay classified on one scale.

  ## Rows are witnesses, not routines

  `symbol` **groups** rows; it is not a key. A routine covered per-form (the
  RLP walk chain proves `rlp_walk_next` separately for the scalar form and for
  account fields 0 and 1) gets one row per theorem. Collapsing those into a
  single row would have to name one theorem as *the* witness for the symbol,
  which would overstate what any one of them proves — the failure mode this
  registry exists to prevent.

  ## Reading `ProofTier` for a routine

  Every triple carries resource preconditions (dword alignment,
  `isValidByteAccess`, non-overflow of `base + len`) and the caller-supplied
  register frame. Those are the ABI, not a gap, and do **not** make a row
  `.conditional`.

  * `.proven` — whole-routine triple, resource/ABI preconditions only.
  * `.conditional` — the same, plus a **nonvacuous input-domain gate** that
    excludes inputs the routine's symbol could otherwise be asked about (an RLP
    short-form `≤ 55` bound, a `SpanForm` restriction). `gate` names it in
    prose so the registry states *what* is excluded rather than hiding it
    behind a tier constructor.

  See `EvmAsm/Progress.lean` for the opcode registry and the witness-`abbrev`
  convention this file follows.
-/

import EvmAsm.Progress
import EvmAsm.Progress.Correspondence
import EvmAsm.Codegen.Programs.U256LtBeSAsm
import EvmAsm.Codegen.Programs.U256EqSAsm
import EvmAsm.Codegen.Programs.U256DivU64BeSAsm
import EvmAsm.Codegen.Programs.U256DivU64BeInPlaceSAsm
import EvmAsm.Codegen.Programs.U256MulU64Be.Whole
import EvmAsm.Codegen.Programs.U256MulU64Be.WholeInPlace
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Proofs.AmbientLiftedFlatTriples
import EvmAsm.Codegen.Proofs.AmbientFreeFlatTriples
import EvmAsm.Codegen.Proofs.CallFrameCalldataFlatTriple
import EvmAsm.Codegen.Proofs.RevLeBeFlatTriples
import EvmAsm.Codegen.Programs.SszPayloadWithdrawalsSAsm
import EvmAsm.Codegen.Programs.SszWitnessStateSAsm
import EvmAsm.Codegen.Programs.EphU32leSAsm
import EvmAsm.Codegen.Programs.SszPackBytesSAsm
import EvmAsm.Codegen.Programs.P256IsZeroNSAsm
import EvmAsm.Codegen.Proofs.FlatBlockPilotSpec
import EvmAsm.Codegen.Proofs.U256IsZeroSpec
import EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceSAsmSupport
import EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceNSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceSAsm
-- #12244: `blsgLeToBeFlat_spec` — the OWN-`CodeReq` triple, in the routine's own
-- module rather than either caller's stage file.
import EvmAsm.Codegen.Programs.Bls12G1LeToBeSAsm
-- Same story one symbol over: `blqZeroFlat_spec` here is the own-`CodeReq` one,
-- NOT the same-named theorem in `Bls12Fq12SetOneSAsm` over the adjacency union.
import EvmAsm.Codegen.Programs.Bls12Fq12ZeroSAsm
import EvmAsm.Codegen.Programs.Bls12Fq12SetOneSAsm
import EvmAsm.Codegen.Programs.Bls12G2Copy192SAsm
import EvmAsm.Codegen.Programs.Bn254Fq12SetOneSAsm
-- The `blsg_be_to_le` triple #12380 landed without rowing.
import EvmAsm.Codegen.Programs.Bls12G1BeToLeSAsm
-- #12244: the own-`CodeReq` entry triples for the two BE↔LE converters, which
-- the caller-anchored `mulCr`/`pdCr` twins are now corollaries of.
import EvmAsm.Codegen.Programs.Secp256k1FieldConvFlatEntry
-- The same, one curve over: the BN254 base-field converters' entry triples.
import EvmAsm.Codegen.Programs.Bn254FieldConvFlatEntry
-- `mset_memcpy_spec_within` — a flat triple all along, behind a file-local base
-- abbrev, which is why the allowlist mis-graded it (#12244).
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
-- `bnq_zero`'s own-`CodeReq` entry triple, split out of the adjacency-`CodeReq`
-- copy that was the only named flat contract for it (#12244).
import EvmAsm.Codegen.Programs.Bn254Fq12ZeroSAsm
-- The four frame-port leaves (#12244). Their flat triples have existed since the
-- FramePort work; `--shape` flags them whole-routine and the allowlist still calls
-- them tier B, which is the stale-tier-column trap in that file's own header.
import EvmAsm.Codegen.Programs.FrameDepthPushSAsm
import EvmAsm.Codegen.Programs.FrameDepthPopSAsm
import EvmAsm.Codegen.Programs.FrameSaveRegsSAsm
import EvmAsm.Codegen.Programs.FrameLoadRegsSAsm
-- The four P-256 leaves (#12244). All four already carry FLAT triples; three of
-- their allowlist entries cited only the structured `Fn_spec` and claimed
-- "needs Fn.retSpecFlat", which had already been applied.
import EvmAsm.Codegen.Programs.P256BeToLeSAsm
import EvmAsm.Codegen.Programs.P256LeToBeSAsm
import EvmAsm.Codegen.Programs.P256CopyNSAsm
import EvmAsm.Codegen.Programs.P256LtBeSAsm
-- The eight BLS12 leaves (#12244): four deterministic copiers, two zeroers, two
-- is-zero predicates. All already flat over their own CodeReq.
import EvmAsm.Codegen.Programs.Bls12Fq12CopySAsm
import EvmAsm.Codegen.Programs.Bls12Fq12IsZeroSAsm
import EvmAsm.Codegen.Programs.Bls12PtCopySAsm
import EvmAsm.Codegen.Programs.Bls12FieldCopyQuadsSAsm
import EvmAsm.Codegen.Programs.Bls12G2Zero192SAsm
import EvmAsm.Codegen.Programs.Bls12G1Copy96SAsm
import EvmAsm.Codegen.Programs.Bls12G1IsZeroNSAsm
import EvmAsm.Codegen.Programs.Bls12G1Zero96SAsm
-- The final nine of the 25 verified-rowable whole-routine triples (#12244).
import EvmAsm.Codegen.Programs.BalGasValidU64SAsm
import EvmAsm.Codegen.Programs.Blake2fLoadLe64SAsm
import EvmAsm.Codegen.Programs.Blake2fStoreLe64SAsm
import EvmAsm.Codegen.Programs.BloomOrIntoSAsm
import EvmAsm.Codegen.Programs.Bls12KzgLtBeSAsm
import EvmAsm.Codegen.Programs.Bn254CallAllotmentSAsm
import EvmAsm.Codegen.Programs.DispatcherCaptureExecStateGasSAsm
import EvmAsm.Codegen.Programs.HpEncodeNibblesSAsm
import EvmAsm.Codegen.Programs.MptResolveCacheResetSAsm
-- The three COMPOSITE CALLERS (#12244). Their union CodeReqs are semantically
-- required — each body `jal`s to its callee — and every component is an image pairing.
import EvmAsm.Codegen.Programs.Bls12G2EncodeSAsm
import EvmAsm.Codegen.Programs.Bls12KzgG2WireSAsm
import EvmAsm.Codegen.Programs.Bn254FieldAddModPSAsm
-- The two MUL twins of the ADD composite above (#12244). Same union shape, and the
-- `--shape` parser could not grade them only because `mulCr` is defined in 3 files.
import EvmAsm.Codegen.Programs.Bn254FieldMulModPSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldMulModPSAsm
-- The guest-address instantiations of the two position-independent witness-index
-- triples (#12244) — a THIRD blocker class: flat and whole-routine but at a free base.
import EvmAsm.Codegen.Proofs.MptWitnessIndexFlatEntry
import EvmAsm.Codegen.Proofs.WitnessCodeLookupSpec
-- First lift of a `model-only` leaf (#12244) — needed an `Fn` change before any
-- adapter applied; see the row's notes.
import EvmAsm.Codegen.Programs.Bn254CurveZeroSAsm
-- The other two 64-byte zeroers, lifted by the same recipe (#12244).
import EvmAsm.Codegen.Programs.Secp256k1PointZero64SAsm
import EvmAsm.Codegen.Programs.Bn254Fp2ZeroSAsm
-- The copier tranche (#12244): non-empty read-only region, so no Region.empty collapse.
import EvmAsm.Codegen.Programs.Bn254CurveCopySAsm
import EvmAsm.Codegen.Programs.Secp256k1PointCopy64SAsm
import EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsm
-- #12319: the pointAdd bridge lives in its own module but reopens the
-- `Secp256k1PointDoubleSAsm` namespace, so the witness abbrev below resolves
-- only with this import present -- the SAsm import above is NOT enough.
import EvmAsm.Codegen.Programs.Secp256k1PointDoubleBridge
import EvmAsm.Codegen.Programs.Bn254Fp2CopySAsm
-- The two DWORD-stepping copiers, completing the family (#12244).
import EvmAsm.Codegen.Programs.Bn254Fq12CopySAsm
import EvmAsm.Codegen.Programs.Bn254PtCopySAsm
-- The is-zero tranche (#12244): EMPTY rw, non-empty read-only region.
import EvmAsm.Codegen.Programs.Bn254Fq12IsZeroSAsm
import EvmAsm.Codegen.Programs.Bn254Fp2IsZeroSAsm
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuardSAsm
-- #12226 harvest: seven flat triples the suffix-based tier heuristic hid.
import EvmAsm.Codegen.Programs.BloomEqSAsm
import EvmAsm.Codegen.Programs.Bls12Fq12EqSAsm
import EvmAsm.Codegen.Programs.Bls12G2EqNSAsm
import EvmAsm.Codegen.Programs.Bn254Fp2EqSAsm
import EvmAsm.Codegen.Programs.Bn254Fq12EqSAsm
import EvmAsm.Codegen.Programs.CallFrameBaseSAsm
import EvmAsm.Codegen.Programs.U256MinSAsm
-- #12659 Stage 2: fee-pricing body and gas-result entry triples.  The former
-- starts after the priority helper's six-instruction entry prologue, so its
-- registry row remains honestly `.partly` until that prologue is composed.
import EvmAsm.Codegen.Programs.U256GasPricingSAsm
import EvmAsm.Codegen.Programs.TxGasResultIncrementsSAsm
import EvmAsm.Rv64.RLP.WalkNextStrict
-- #12799 rows 1 and 2: the two canonical-strict content decoders, instantiated
-- at their own `GuestAddrs` so the `CodeReq` is the image claim rather than a
-- position-independent one. The free-base proofs live in `Rv64/RLP/ContentTo*`;
-- this module is only the anchoring plus the four non-vacuity witnesses.
import EvmAsm.Codegen.Proofs.RlpContentStrictAtGuest
-- #12033: the machine tie for the STRICT wrapper relation.
import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie
import EvmAsm.Codegen.Programs.RlpWalkNextEntryTie
import EvmAsm.Codegen.Programs.RlpWalkNextLeafTie
import EvmAsm.Codegen.Programs.HeaderArityCheckTie
import EvmAsm.Codegen.Programs.RlpWalkInitTie
-- #12300: the strict LIST cycle's fuel relation and CPS arm contracts.
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuel
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelListArm
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachine
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineCont
import EvmAsm.Codegen.Programs.BloomOrIntoBridge
import EvmAsm.Evm64.AccountAccessorSpec
import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm
import EvmAsm.Codegen.Programs.RlpEncodeBytesComposeSAsm
import EvmAsm.Codegen.Programs.RlpEncodeBytesComposeTailSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Programs.RlpItemSpanBody
import EvmAsm.Codegen.Programs.RlpItemSpanLong
-- #10780 item 3: the 2-length-byte long form, in a sibling module because
-- RlpSpliceHelperSpec is at the 1500-line cap.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong2Spec
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeSAsm
import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeBridge
import EvmAsm.Codegen.Programs.HeaderExtractNumberSpec
import EvmAsm.Codegen.Programs.HeaderFieldsSpec
import EvmAsm.Codegen.Programs.ValidateHeader
import EvmAsm.Codegen.Programs.HeaderReceiptsRootSpec
import EvmAsm.Codegen.Programs.HeaderWithdrawalsRootSpec
import EvmAsm.Codegen.Programs.BlockHashFromWitnessHeadersSpec
import EvmAsm.Codegen.Programs.HeaderU64ExtractSpec
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeCopy
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeWalkSite
-- #12461 item 10: K73 arm-indexed seams. Keep the route import explicit so
-- the registry directly forces the route composition theorem; check-unimported
-- only checks transitive reachability. The Entry import makes the new banked
-- module explicit too, without adding a registry row or changing counts.
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeRoutes
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderExtractLogsBloomBridge
import EvmAsm.Codegen.Programs.HeaderValidateExtraDataLengthBridge
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeBridge
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeBridgeWitness
import EvmAsm.Codegen.Programs.HeadersParentHashMain
import EvmAsm.Codegen.Programs.HeaderValidateParentHashUnified
-- #12799: the three full-premise cover witnesses for the hvph dispatcher were
-- outside the axiom gate entirely — no witness abbrev, and this module did not
-- import theirs. A `.proven` row whose satisfiability evidence no gate forces
-- is exactly the shape the discipline exists to prevent, so they are imported
-- and abbrev'd below.
import EvmAsm.Codegen.Programs.HeaderValidateParentHashUnifiedCover
import EvmAsm.Codegen.Programs.HeaderExtractNumberBridge
import EvmAsm.Codegen.Programs.AccountDecodeCompose
-- #11516: AccountDecodeCompose imports AccountDecodeBridge, not Close6, so the
-- whole-routine triple's module has to be imported explicitly for its witness.
import EvmAsm.Codegen.Programs.AccountDecodeClose6
-- #12108: the `zkvm_keccak256_segments` whole-routine triple (the gather
-- entry point `tx_signing_hash` hashes through).
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTop
import EvmAsm.Codegen.Programs.AccountAccessorNonceSpec
import EvmAsm.Codegen.Programs.AccountAccessorTopSpec
import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose6
import EvmAsm.Codegen.Programs.ReceiptExtractLogsBloomSpec
import EvmAsm.Codegen.Programs.AccountEip161LeniencyBridge
import EvmAsm.Codegen.Programs.RlpFieldToU256BeWholeSAsm
import EvmAsm.Codegen.Programs.RlpFieldToU64WholeSAsm
import EvmAsm.Codegen.Programs.RlpListEncodedSizeSAsm
import EvmAsm.Codegen.Programs.RlpListEncodedSizeBridge
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsm
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixCanonical
import EvmAsm.Codegen.Programs.RlpItemSizeLongSpec
import EvmAsm.Codegen.Programs.RlpItemSizeTotalSpec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLoopSpec
-- #10817: `bal_canonical_sort`'s nibble extractor against a SEMANTICALLY decoded
-- key. A block lemma over the whole routine's `CodeReq`, not a routine triple.
import EvmAsm.Codegen.Programs.BalCanonicalSortDigitSpec
-- #10780 item 3, next width: the 3-length-byte long form, first arm to cite
-- `lpLolLoop` instead of unrolling the length-byte loop.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong3Spec
-- #10780 item 3, next width: the 4-length-byte long form. Long3's ladder with
-- ONE more fall-through, plus `lpLolLoop` cited at `m := 4`.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong4Spec
-- #10780 item 3, widths 5/6/7: each is long4's ladder with one more fall-through
-- per width, plus `lpLolLoop` cited at `m := 5`/`6`/`7`. `lenlen = 8` is NOT here —
-- its loop overflow side condition needs `outPtr.toNat + 9 ≤ 2 ^ 64`, which is one
-- byte more than `outPtr.toNat % 8 = 0` supplies.
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong5Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong6Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong7Spec
import EvmAsm.Codegen.Programs.RlpEncodeListPrefixLong8Spec
-- #12038 / #12324: K145 `tx_signing_hash` whole-routine short-domain triple
-- (preimage ≤135, single-rate-block via `zkvm_keccak256_segments`).
import EvmAsm.Codegen.Programs.TxSigningHashSpec
-- #12038 opening move on the signing-hash lane: the K147 EIP-7702
-- authorization-signing-hash wrapper, whole-routine, under a named
-- unproven-callee residual for K145 `tx_signing_hash`.
import EvmAsm.Codegen.Programs.Eip7702AuthSigningHashTop
import EvmAsm.Codegen.Programs.AccountDecodeCorrespondence
import EvmAsm.Codegen.Programs.SpecRefConstantPins
import EvmAsm.Codegen.Programs.RlpListCountItemsBridge
import EvmAsm.Codegen.Programs.BgvU32leSpec
import EvmAsm.Codegen.Programs.ExecutionRequestsHashBgvOffset
import EvmAsm.Codegen.Programs.CheckGasLimitBridge
import EvmAsm.Codegen.Programs.BytesToNibblesBridge
import EvmAsm.Codegen.Programs.WithdrawalDecodeClose5
import EvmAsm.Codegen.Programs.CryptoFieldLtPBridge
-- #11799 dep: whole-routine mpt_node_kind machine triple (Wrap holds the capstone).
import EvmAsm.Codegen.Programs.MptNodeKindWrap
import EvmAsm.Codegen.Programs.MptNodeKindWire
-- #11800 node-DB half: whole-routine machine triple for `node_db_lookup`.
import EvmAsm.Codegen.Programs.NodeDbLookupSpec
-- #12036: `witness_lookup_by_hash` ABI frame, telemetry idiom, and the
-- whole-routine triple on the `section_len = 0` domain.
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledOneHit
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledWrap
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledOneHitWrap
import EvmAsm.Codegen.Programs.MptWalkWlEnabledEmpty
import EvmAsm.Codegen.Programs.MptWalkWlEnabledHit
import EvmAsm.Codegen.Programs.MptWalkWlEnabledHitSat
import EvmAsm.Codegen.Programs.ExecutionRequestsHashWrap
-- #12011 hash-half: erh_hash_one empty+nonempty tops under residual h_sha
-- (no whole-routine row yet; witnesses still required for axiom gate).
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneTop
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneNonemptyTop
-- #12206: `assemble_execution_requests` whole-routine triple.
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsTop
import EvmAsm.Codegen.Programs.RequestsHashVerifyTop
import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsmPaths
import EvmAsm.Codegen.Programs.HpDecodeCompactBridge
-- #11575 tier A: the whole-routine triples live in the `LoopClose` modules (the
-- `Spec` modules hold only the prologue/epilogue/return-path blocks), so it is
-- those that have to be imported for the witness abbrevs to force.
import EvmAsm.Codegen.Programs.ChainValidateConsecutiveNumbersLoopClose
import EvmAsm.Codegen.Programs.ChainValidatePostMergeFullSpec
-- #12488: `ChainValidatePostMergeFullLoop` (ghost∪live `firstCall_disjoint`)
-- deleted — its only consumer was this unused import. The empty-domain
-- whole-routine witness below lives in `…FullSpec` and uses ghost `cvpmfCode`
-- alone, so the allowlist entries stay. The three LoopClose imports for
-- gul/bgm/bgum are gone with those composites (no Progress row, no allowlist).
import EvmAsm.Codegen.Programs.ChainValidateIncreasingTimestampsLoopClose
import EvmAsm.Codegen.Programs.TxTypeDispatchTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Codegen.Programs.BlockHashFromHeaderSpec
import EvmAsm.Codegen.Programs.BlockAccessListHashCoreSpec
import EvmAsm.Codegen.Programs.SszWitnessStateSectionSpec
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeFinal
import EvmAsm.Codegen.Proofs.HashBridgeSha256Frame
import EvmAsm.Codegen.Proofs.HashBridgeSha256Setup
import EvmAsm.Codegen.Proofs.HashBridgeSha256Block
import EvmAsm.Codegen.Proofs.HashBridgeSha256Outer
-- #12018: whole-routine `zkvm_sha256_spec_within` (flat CodeReq.ofProg at the
-- guest address; SpecRef post via `sha256BodyDigest_eq_specref`).
import EvmAsm.Codegen.Proofs.HashBridgeSha256Top
import EvmAsm.Codegen.Programs.AddressFromPubkeySpec
-- #12222: `accountReadRecordSuppressedFlat_spec` — the BAL read-half producer's
-- suppressed arm, whole-routine at `GuestAddrs.account_read_record`.
import EvmAsm.Codegen.Proofs.AccountReadRecordSpec

namespace EvmAsm.Progress

/-- One row of the guest-routine registry: a **witness theorem** for a claim
    about a linked guest symbol.

    `symbol` groups rows rather than keying them — see this module's header on
    why a per-form routine gets one row per theorem. -/
structure RoutineEntry where
  /-- The guest symbol the claim is about, as it appears in the linked image
      (`rlp_encode_uint_be`, `rlp_item_size`, …). Not unique across rows. -/
  symbol : String
  /-- Verification depth, on the same `ProofTier` scale as the opcode
      registry. See this module's header for how the tiers read for a
      routine. -/
  tier : ProofTier
  /-- Witness theorem name, unqualified. Every row's `proofRef` must have a
      matching witness `abbrev` below — `scripts/gen-axiom-witnesses.py`
      cross-checks this and fails loudly on a row without one, because a row
      whose theorem is never forced is a row the axiom gate cannot see. -/
  proofRef : Option String
  /-- For a `.conditional` row: the input-domain gate, in prose. Empty for
      `.proven`. Stated so the registry says what is excluded rather than
      leaving it to be discovered in the theorem statement. -/
  gate : String := ""
  /-- Optional short note for the rendered report. -/
  notes : String := ""
  deriving Repr

/-- Smart constructor for a routine row, mirroring `EvmAsm.Progress.entry`
    (`Progress.lean`) so the defaulted trailing fields stay omittable — the
    anonymous `⟨…⟩` constructor cannot skip them. -/
def routine (symbol : String) (tier : ProofTier) (proofRef : Option String)
    (gate : String := "") (notes : String := "") : RoutineEntry :=
  { symbol, tier, proofRef, gate, notes }

/-! ## Registry

    Grouped by guest symbol. This is a **partial** enumeration of the verified
    guest surface — see `routineCount` below and the module docstring in
    `EvmAsm/Progress/AxiomWitnesses.lean` for what is not yet covered. -/
def routineRegistry : List RoutineEntry := [
  -- `rlp_encode_uint_be` — the routine whose uncovered triple surfaced #11042.
  routine "rlp_encode_uint_be" .conditional (some "reub_spec_within")
      (gate := "stripped payload `n - reubZeros xs 0 n ≤ 55` — the RLP "
        ++ "short-form bound. Above it the header byte is still computed as "
        ++ "specified but stops being an RLP header, so the routine is out of "
        ++ "domain rather than wrong")
      (notes := "whole-routine triple over the routine's own `reubOut` model; "
        ++ "all three paths (all-zero, raw single byte, header) proved and each "
        ++ "shown to fire on its own inputs"),
  routine "rlp_encode_uint_be" .conditional (some "reub_spec_encode_within")
      (gate := "same `≤ 55` short-form bound as `reub_spec_within`")
      (notes := "the same triple restated against the reference encoding "
        ++ "`encodeBytes (Nat.toBytesBE (Nat.fromBytesBE xs))`, so the claim is "
        ++ "against RLP rather than against the module's own model. The "
        ++ "reference is this repo's Lean port, not the pinned Python — a "
        ++ "port/Python divergence would not be visible here"),
  routine "rlp_encode_uint_be" .conditional (some "reub_spec_within_of_length_le")
      (gate := "`n ≤ 55` — strictly stronger than the tight bound, and the "
        ++ "form a caller can discharge without reasoning about `reubZeros`")
      (notes := "ABI-shaped corollary; every production caller passes 8 or 32"),

  -- `rlp_encode_bytes` — #10780 item 2. Total function: no input-domain
  -- restriction, so `.proven` where `reub` is `.conditional` — both sides of
  -- the 55/56 boundary are inside the claim.
  routine "rlp_encode_bytes" .proven (some "reb_spec_within")
      (notes := "whole-routine triple against `encodeBytes` — the function "
        ++ "SpecRef's own encoders call (`encR := EL.RLP.encode`, and "
        ++ "`encode (.bytes d) = encodeBytes d` definitionally). All three "
        ++ "paths (raw byte, short form, long form) proved; coverage examples "
        ++ "pin output bytes as literals on both sides of 55/56. Resource "
        ++ "preconditions only (capacity `n + 9`, alignment, validity)"),
  routine "rlp_encode_bytes" .proven (some "reb_spec_rlpItem_within")
      (notes := "the same triple with the output region phrased as "
        ++ "`rlpItemRegionFrom outPtr (.bytes data) …` — the `RLPItem` "
        ++ "vocabulary a caller encoding a SpecRef struct field composes with"),

  -- `rlp_item_size` — at its linked guest address, unlike the ∀-base walk triples.
  routine "rlp_item_size" .conditional (some "rlp_item_size_spec_within")
      (gate := "`SpanForm (bs.getD 0 0)` — single byte, short string and short "
        ++ "list forms. The `lenlen ≥ 2` long forms are the documented cut "
        ++ "(#10780 item 3)")
      (notes := "stated at `rlpItemSizeBase = GuestAddrs.rlp_item_size`, the "
        ++ "form the `rlp_item_span` / `mpt_splice_slot` compositions consume"),
  -- #10780 item 3: the two arms `SpanForm` excludes, proved per-form rather than by
  -- widening the gate (`SpanForm` has 50+ consumers; widening it is separate work).
  -- Both cite `risLenLoop` for the length-byte loop instead of unrolling it, so each is
  -- its dispatch path plus the shared idx22-34 tail.
  routine "rlp_item_size" .conditional
      (some "rlp_item_size_long_string_pinned_spec_within")
      (gate := "`0xb8 ≤ p < 0xc0` — the long-string form, one of the two arms "
        ++ "`SpanForm` excludes. Input-domain only; coverRef "
        ++ "`longStringSample_reachable` exhibits the SMALLEST such item (a "
        ++ "56-byte string, exactly the short/long boundary) and checks its span "
        ++ "identity, so the arm is not reachable only in the large")
      (notes := "per-form pinned triple; `a0 = 1 + lenOfLen + fromBytesBE lenBytes`, "
        ++ "spelled in the model's own `rlpPrefixLongBytesLenOfLen` vocabulary. Step "
        ++ "bound `7*lenOfLen + 17`. ⭐ Full identification with `(encode item).length` "
        ++ "is the separate corollary `…_encode_length_spec_within`, because it needs "
        ++ "`decode`/`readLength` facts a machine triple cannot manufacture — folding "
        ++ "them into the triple would have been a weakening"),
  routine "rlp_item_size" .conditional
      (some "rlp_item_size_long_list_pinned_spec_within")
      (gate := "`p ≥ 0xf8` — the long-list form, the other `SpanForm` exclusion. "
        ++ "coverRef `longListSample_reachable`. Every block header RLP is a long "
        ++ "list, so this arm is on the common path, not an edge case")
      (notes := "per-form pinned triple, step bound `7*lenOfLen + 18` (one dispatch "
        ++ "step more than the long-string arm). The payload's own well-formedness is "
        ++ "NOT part of the gate: `rlp_item_size` computes a span and does not descend"),
  -- #11577: whole-routine span under short-list outer + WalkedSpanForm on
  -- every walked prefix. Lifts the leaf-routine-targets exclusion (verified
  -- set includes .conditional). Callers inherit the SpanForm domain.
  routine "rlp_item_span" .conditional (some "rlp_item_span_spec_within")
      (gate := "short-list outer (`payloadLen items ≤ 55`) and "
        ++ "`WalkedSpanForm items i` (SpanForm on every walked item 0..i, "
        ++ "including the target). Long-list outer header and non-SpanForm "
        ++ "walked items uncovered. coverRef "
        ++ "`rlp_item_span_precondition_reachable`")
      (notes := "stated at `rlpItemSpanBase = GuestAddrs.rlp_item_span`; "
        ++ "callee size via offset-framed `rlp_item_size_offset_spec_within`"),
  -- #10780: the LONG outer-header arm, and the dispatch that makes the
  -- outer header total. The walk cursor is now `listCursor`, whose header
  -- length comes from `hdrLen`, so the loop/exit/store blocks are shared
  -- verbatim; only the header block is form-specific.
  routine "rlp_item_span" .conditional (some "rlp_item_span_long_spec_within")
      (gate := "`56 ≤ payloadLen items` — the LONG outer header "
        ++ "(`0xF7 + lenlen`), plus the same `WalkedSpanForm items i`. ALL "
        ++ "widths at once, not per `lenlen`: `long_lenlen_le_8` bounds "
        ++ "`lenlen ≤ 8` from `h_over` alone, so `SUB`/`ADDI` compute "
        ++ "`hdrLen` for every width. NOT covered: non-canonical long "
        ++ "headers — the guest checks neither `bs[1] ≠ 0` nor "
        ++ "`payloadLen ≥ 56` (both spec-decoder conditions, `rlp.py:436` "
        ++ "and `:441`), and the domain `bs = encode (.list items)` makes "
        ++ "them hold by construction, so nothing is claimed about "
        ++ "REJECTING a malformed header. coverRef "
        ++ "`rlp_item_span_long_precondition_reachable` (56 × `.bytes []`, "
        ++ "the SMALLEST long payload), strengthened by "
        ++ "`rlp_item_span_long_bundle_satisfiable`, which satisfies the "
        ++ "domain gate AND every ABI/resource premise at once at a "
        ++ "concrete `listBase`; negative controls "
        ++ "`long_gate_negative_control` (the short witness refutes the "
        ++ "gate) and `long_walk_negative_control` (a long-header list "
        ++ "whose item is NOT `SpanForm`, so the two conjuncts are "
        ++ "independent)")
      (notes := "step bound `38 + 19*i` — four more than the short arm's "
        ++ "`34 + 19*i`, the twelve header instructions idx14..24,26 versus "
        ++ "eight. Lives in `Codegen/Programs/RlpItemSpanLong.lean`"),
  routine "rlp_item_span" .conditional
      (some "rlp_item_span_any_header_spec_within")
      (gate := "`WalkedSpanForm items i` ONLY — the outer-header form is no "
        ++ "longer gated. Dispatches on the decidable, exhaustive split "
        ++ "`payloadLen items ≤ 55`, so it holds for EVERY canonically "
        ++ "encoded list; the residual on this routine is now exactly the "
        ++ "walked-item domain (non-`SpanForm` items) plus the ABI/resource "
        ++ "premises. coverRefs: both arms' reachability lemmas above")
      (notes := "stated at the long arm's bound `38 + 19*i`, which dominates "
        ++ "the short arm's; `cpsTripleWithin` is an upper bound on steps, "
        ++ "so the short branch weakens into it via "
        ++ "`cpsTripleWithin_mono_nSteps`"),

  -- The RLP walk chain / account accessors.
  routine "rlp_walk_init" .proven (some "account_rlp_walk_init_spec_within")
      (notes := "∀-base triple over `rlp_walk_init_code`; opens an "
        ++ "`encodeAccount` list and leaves the field cursor at `listBase + 2`. "
        ++ "⚠️ This is the ACCOUNT-SPECIALISED triple. The form-generic routine "
        ++ "spec is a different theorem — `EvmAsm.Rv64.RLP.rlp_walk_init_"
        ++ "spec_within` (`Rv64/RLP/WalkInit.lean`) — witnessed via the "
        ++ "correspondence registry, not from here. Two theorems share the "
        ++ "unqualified name; do not read either as the other"),
  routine "rlp_walk_init" .conditional (some "rlp_walk_init_long1_spec_within")
      (gate := "`56 ≤ payload.length` — the long-form-1 arm specifically")
      (notes := "per-form companion to the account triple above"),
  -- #12799 ownership-table row 8: the OWN-ANCHORED contract. The two rows above
  -- are both unusable by a caller at `GuestAddrs.rlp_walk_init` — one is
  -- ∀-base AND account-specialised, the other gates on the long-form-1 arm.
  -- This row RE-ANCHORS the form-generic nine-outcome triple at the linked
  -- entry; the generic theorem's `base` is a plain `Word` with no side
  -- conditions, so no proof obligation survives the instantiation.
  routine "rlp_walk_init" .proven (some "rlp_walk_init_entry_spec_within")
      (notes := "`cpsTripleWithin 81` at `GuestAddrs.rlp_walk_init` over "
        ++ "`CodeReq.ofProg I rlp_walk_init_prog` (53 insns = the linked 212-byte "
        ++ "extent). All NINE outcomes: statuses 1..7 plus the short and long "
        ++ "success shapes. NOT form-specialised — no `encodeAccount` anywhere. "
        ++ "Premises are the usual readability ones, with the long-header trio "
        ++ "`hll_len`/`hll_over`/`hll_valid` guarded by `prefix ≥ 0xf8 ∧ header "
        ++ "fits`. coverRef `rlp_walk_init_entry_instance`, a closed 58-byte "
        ++ "LONG-form-1 list that reaches those premises with their antecedents "
        ++ "TRUE, plus `rlp_walk_init_entry_hyps_refutable` as the negative "
        ++ "control. ⚠️ `rlp_walk_init` has NO `guestImageEntries` pairing and "
        ++ "cannot get one without #12686: `rlpWalkInitFunction` reaches its "
        ++ "Program through the QUALIFIED name `EvmAsm.Rv64.RLP.rlp_walk_init_"
        ++ "prog`, which `scripts/guest_image_coverage.py` rejects by design. "
        ++ "The anchor here does not need it — it is the same "
        ++ "`CodeReq.ofProg <GuestAddrs entry> <Program>` shape "
        ++ "`rlp_walk_next_shared` uses"),
  routine "rlp_walk_next" .proven (some "account_rlp_walk_next_field0_spec_within")
      (notes := "field 0 (nonce) of an `encodeAccount` list. The form-generic "
        ++ "`EvmAsm.Rv64.RLP.rlp_walk_next_spec_within` is a distinct theorem, "
        ++ "witnessed via the correspondence registry"),
  routine "rlp_walk_next" .proven (some "account_rlp_walk_next_field1_spec_within")
      (notes := "field 1 (balance) of an `encodeAccount` list"),
  routine "rlp_walk_next" .conditional (some "rlp_walk_next_scalar_spec_within")
      (gate := "`(Nat.toBytesBE n).length ≤ 55` — scalar short form")
      (notes := "form-generic scalar arm, not tied to `encodeAccount`"),
  -- #12799 ownership-table row 3: a contract for the THUNK at
  -- `GuestAddrs.rlp_walk_next` itself. ⚠️ The three rows above cite theorems
  -- over `rlp_walk_next_code base` — free base, and the CORE's 103-instruction
  -- program (`rlp_walk_next_prog`), not the 13-instruction thunk
  -- (`rlpWalkNext_prog`). They say nothing about the routine the 19
  -- `header_extended_decode` call sites actually enter.
  routine "rlp_walk_next" .conditional
      (some "rlp_walk_next_entry_nonlist_strict_spec_within")
      (gate := "the item's prefix byte is `< 0xc0` (a byte string, not a list) — "
        ++ "INHERITED unchanged from `rlp_walk_next_shared_nonlist_strict_spec_"
        ++ "within`, which is COMPOSED here, not assumed; the LIST arms (the runs "
        ++ "that enter `rlp_validate_payload`) are not covered. The shared body's "
        ++ "OTHER gate, `s0 ≥ 2`, IS discharged here: the thunk sets "
        ++ "`s0 = (a1 - a0) <<< 1` (idx 4/5), so the gate becomes `endPtr` is a "
        ++ "valid guest byte address and `cursor < endPtr`, i.e. `a1 - a0 ≥ 1`. "
        ++ "coverRef `rlp_walk_next_entry_instance` + "
        ++ "`rlp_walk_next_entry_accept_reachable`; negative control "
        ++ "`rlp_walk_next_entry_hyps_refutable`")
      (notes := "`cpsTripleWithin 122` (8 thunk + 109 shared + 5 thunk) at "
        ++ "`GuestAddrs.rlp_walk_next` over `CodeReq.ofProg T rlpWalkNext_prog` "
        ++ "unioned with `RlpWalkNextStrictTie.fullCode` (shared ∪ core) — three "
        ++ "linked extents, nothing else. Post carries `rlpItemDecodeStrictW` on "
        ++ "the accept arm, inherited from the shared body. Every pinned register "
        ++ "is read off one of the thirteen disassembled lines; `x6`/`x7`/`x12`/"
        ++ "`x13`/`x28..x31` appear only because the CALLEE requires or clobbers "
        ++ "them. Lives in `Codegen/Programs/RlpWalkNextEntryTie.lean`"),
  -- #12799 ownership-table row 4: the leaf-only cursor wrapper the header
  -- checker calls.  Extent derived from `nm` + next symbol
  -- (`0x8000bb28`→`0x8000bb64`, 60 B) and cross-checked against
  -- `rlpWalkNextLeaf_prog.length * 4 = 15 * 4 = 60`.
  routine "rlp_walk_next_leaf" .conditional
      (some "rlp_walk_next_leaf_entry_nonlist_strict_spec_within")
      (gate := "the item's prefix byte at the INPUT cursor is `< 0xc0` — "
        ++ "INHERITED unchanged from `rlp_walk_next_entry_nonlist_strict_spec_"
        ++ "within` (row 3), which is COMPOSED here, not assumed. ⛔ The "
        ++ "routine's OWN prefix test (idx 10, `bltu t2,192`) does NOT discharge "
        ++ "this gate: it runs AFTER the `jal` (idx 3), so it cannot restrict the "
        ++ "callee's input domain, and it tests the byte at `t0 = a0 - a2`, an "
        ++ "address computed from the callee's OUTPUTS, not `srcBytes[srcOff]`. "
        ++ "What it does buy is `prefix_test_always_taken`: under the gate the "
        ++ "test is ALWAYS taken, so idx 11 (`li a1,8`) is DEAD and the wrapper "
        ++ "is status-transparent — the `a1` returned is the walker's own, never "
        ++ "the wrapper's 8. Covering status 8 needs the walker's LIST arms, i.e. "
        ++ "exactly what row 3 does not cover. coverRef "
        ++ "`rlp_walk_next_leaf_entry_instance` (path B, three-byte short string) "
        ++ "+ `rlp_walk_next_leaf_single_byte_instance` (path C, the run that "
        ++ "actually executes the prefix test) + "
        ++ "`rlp_walk_next_leaf_prefix_test_instance`; negative control "
        ++ "`rlp_walk_next_leaf_premises_refutable`. ⭐ Composing row 3 here "
        ++ "surfaced a TENTH premise on it, `hll` (the long-LIST readability "
        ++ "side-condition), that constrained nothing: `hnotlist` puts the byte "
        ++ "below `0xc0`, hence below `0xf8`, so `hll`'s own antecedent is "
        ++ "unsatisfiable on the domain. FIXED UPSTREAM in `lane-b4` 6925938c9 "
        ++ "-- `hll` removed from row 3's statement (ten premises to nine) and "
        ++ "discharged there by `ult_f8_of_ult_c0`. This row inherits the "
        ++ "corrected nine-premise statement and neither carries `hll` nor "
        ++ "re-proves the bridge")
      (notes := "`cpsTripleWithin 136` (3 prologue + 1 + 122 jal/walker + 10 "
        ++ "tail) at `GuestAddrs.rlp_walk_next_leaf` over `CodeReq.ofProg L "
        ++ "rlpWalkNextLeaf_prog` unioned with `RlpWalkNextEntryTie.wholeCode` "
        ++ "(thunk ∪ shared ∪ core) — four linked extents, nothing else. Post "
        ++ "carries `rlpItemDecodeStrictW` on the accept arm, inherited unchanged "
        ++ "from row 3. Every pinned register is read off one of the fifteen "
        ++ "disassembled lines; `x0`/`x8`/`x9`/`x13`/`x29..x31` appear only "
        ++ "because the CALLEE requires or clobbers them. Lives in "
        ++ "`Codegen/Programs/RlpWalkNextLeafTie.lean`"),
  -- #12257 phase mover: the complete core triple predates the Codegen
  -- transcription, but its code parameter was generic. The Codegen-side tie
  -- identifies that verified body with the GuestAddrs-anchored core Program
  -- without pinning the numeric address. This row is intentionally the
  -- lenient CORE contract; the strict recursive wrapper remains open.
  routine "rlp_walk_next_core" .proven
      (some "rlp_walk_next_spec_within")
      (notes := "complete lenient core triple, anchored symbolically by "
        ++ "`rlpWalkNextCoreCode_eq_verified`; its list arms are span-fit only. "
        ++ "The strict LIST validator (`rlp_walk_next_shared → "
        ++ "rlp_validate_payload → shared`) is not covered "
        ++ "by this row and remains the recursive proof residual"),
  -- #12300: the validator entry is tied to the strict LIST-cycle model, but
  -- the machine CPS continuation remains an explicit caller premise.
  routine "rlp_validate_payload" .conditional
      (some "rlp_validate_payload_cps_under_shared")
      (gate := "caller supplies the CPS contract `hshared` for the recursive "
        ++ "shared arm; `cycleFuel_mutual_strong_induction` discharges the "
        ++ "structural fuel family, but the instruction-level continuation "
        ++ "is not yet derived from it. The surviving witness is explicitly "
        ++ "offline: it quantifies over `rlpValidatePayloadOffline_prog` and "
        ++ "the synthetic `rlpWalkNextNestedOfflineAddr`, whose 23-instruction "
        ++ "Program is not byte-identical to the linked 21-instruction "
        ++ "`rlpValidatePayload_prog`; this row does not claim production-image "
        ++ "correspondence. This is a DOWNGRADE relative to main forced by the "
        ++ "legacy strict-fuel contract's V+36→V+40 nested-JAL shape: the shipped "
        ++ "21-instruction RecDecode adapter has no such edge, so retaining the "
        ++ "production anchor would not state the existing CPS theorem. Re-proving "
        ++ "that production-image contract is tracked by #12661")
      (notes := "entry contract covers empty, precheck-failure, nested-failure "
        ++ "and continuation tails under the explicit shared-arm contract; the "
        ++ "terminal `NestedFuel.done` case models the exact cursor=end check"),
  -- #12033: the STRICT wrapper, tied to the machine. This is the first row whose
  -- post carries `rlpItemDecodeStrictW` rather than the core's lenient
  -- `rlpItemDecode`; every other `rlp_walk_next*` row above consumes the 412-byte
  -- core only. The gate is an INPUT-DOMAIN gate, not an unproven callee: the one
  -- callee this triple has (`rlp_walk_next_core`) is proven by
  -- `EvmAsm.Rv64.RLP.rlp_walk_next_spec_within` and is composed here, not assumed.
  routine "rlp_walk_next_shared" .conditional
      (some "rlp_walk_next_shared_nonlist_strict_spec_within")
      (gate := "the item's prefix byte is `< 0xc0` (a byte string, not a list) and "
        ++ "the wrapper's recursion budget `s0` is `≥ 2`; the LIST arms now have "
        ++ "a strict `cycleFuel` mutual witness, but their CPS continuation still "
        ++ "requires the explicit `hshared` adapter premise. coverRef "
        ++ "`rlp_walk_next_shared_nonlist_strict_instance`, which also exhibits a "
        ++ "closed `rlpItemDecodeStrictW` witness so the accept disjunct is not vacuous")
      (notes := "`cpsTripleWithin 109` over `CodeReq.ofProg GuestAddrs."
        ++ "rlp_walk_next_shared rlpWalkNextShared_prog` unioned with the core at "
        ++ "`GuestAddrs.rlp_walk_next_core`; post carries `rlpItemDecodeStrictW` as a "
        ++ "CONCLUSION. The recursive-payload conjunct is discharged by the wrapper's "
        ++ "OWN prefix load (index 13) and `bltu t1, 0xc0` (index 15), not by a "
        ++ "model-side bridge — `rlpItemDecodeStrictW_to_decodeAux` CONSUMES that "
        ++ "conjunct and so cannot supply it. Reject arms (core status 2..6) are "
        ++ "covered too, carrying `a1 ≠ 0` only"),
  -- #12300: the separate LIST-arm row; it is not hidden inside the non-LIST
  -- row above because the recursive CPS adapter remains a distinct premise.
  routine "rlp_walk_next_shared" .conditional
      (some "shared_list_arm_contract_from_adapter")
      (gate := "LIST prefix (`pfx ≥ 0xc0`); the structural `cycleFuel` family is "
        ++ "closed, but the short/long CPS contracts and validator continuation "
        ++ "must still be supplied through `SharedListValidatorAdapter`")
      (notes := "LIST branch composition at `S+84`, merging the short arm at "
        ++ "`S+148` and long arm at `S+88`; `NestedFuel.done` handles the exact "
        ++ "cursor=end terminal case") ,
  routine "rlp_content_to_u64" .conditional
      (some "account_rlp_content_to_u64_nonce_spec_within")
      (gate := "`a.nonce < 2 ^ 64` — the accessor's u64 output width, narrower "
        ++ "than `Account.nonce`'s own `< 2 ^ 256` invariant")
      (notes := "step bound `7 * (Nat.toBytesBE a.nonce).length + 11`"),
  routine "rlp_content_to_u256_be" .proven
      (some "account_rlp_content_to_u256_be_balance_spec_within")
      (notes := "writes the 32-byte balance; step bound "
        ++ "`7 * (Nat.toBytesBE a.balance.toNat).length + 16`"),

  -- #12799 rows 1 and 2. ⚠️ These are NOT the two rows above. Four distinct
  -- symbols live within 0x108 bytes of each other in the image — `rlp_content_to_u64`
  -- (0x80005310), `rlp_content_to_u256_be` (0x80005358), and the two `_strict`
  -- variants below — and it is the `_strict` pair that the typed-scalar decoders
  -- (`header_extended_decode` x6 + x1, `header_extended_decode_arity_check` x1 + x1)
  -- actually call. Neither had a row until now; the two lenient rows above were
  -- covering a different guest.
  --
  -- Both are `.proven`, not `.conditional`: every hypothesis is a resource/ABI
  -- fact known statically before the call (dword alignment of the input region,
  -- the buffer holds the `len` bytes, non-overflow, `isValidByteAccess`), and
  -- there is NO input-domain gate — all four exit paths are in the post, the
  -- rejects included, so the triple answers for every length and every byte
  -- string. That is the coverage gate's own tier A.
  routine "rlp_content_to_u64_strict" .proven
      (some "rlp_content_to_u64_strict_at_guest_spec_within")
      (notes := "whole-routine `cpsTripleWithin (7 * len + 11)` over "
        ++ "`CodeReq.ofProg GuestAddrs.rlp_content_to_u64_strict "
        ++ "rlp_content_to_u64_strict_prog` (22 instructions, 0x800053c0..0x80005414). "
        ++ "ALL FOUR exit paths, one per `ret` in the listing: `8 < len` → a1=2 "
        ++ "(0x80005414); `len = 0` → a0=a1=0 (0x80005400, ACCEPT — empty content is "
        ++ "the canonical RLP zero); `0 < len ≤ 8 ∧ content[0] = 0` → a1=3 "
        ++ "(0x80005408); otherwise a1=0 and a0 = fromBytesBE content (0x80005400). "
        ++ "Frameless leaf, zero callees, no `sp` traffic. Frame pinned from the "
        ++ "disassembly: writes a0 a1 t0 t1 t2 t3 (x10 x11 x5 x6 x7 x28) and NOTHING "
        ++ "else; ra preserved; no memory written. The single loop (back edge "
        ++ "`j 0x800053e0` at 0x800053f8) decreases on the t2/x7 remaining counter. "
        ++ "coverRef `rlp_content_to_u64_strict_at_guest_instance` (accept arm live) "
        ++ "with negative control `rlp_content_to_u64_strict_at_guest_negative_control`. "
        ++ "⚠️ This is NOT `EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_spec_within`, "
        ++ "which is the same contract at a FREE base and so is not the image claim; "
        ++ "this row cites the anchored corollary. ⚠️ The symbol still has no "
        ++ "`guestImageEntries` pairing, so the whole-guest byte-identity gate does "
        ++ "not cover it — blocked by #12686 (the body reaches its program through a "
        ++ "qualified name, which `guest_image_coverage.py` refuses). Byte identity "
        ++ "rests instead on the `rfl`-checked emission identity "
        ++ "`rlpContentToU64StrictFunction_eq_verified_prog` plus a manual objdump read"),
  routine "rlp_content_to_u256_be_strict" .proven
      (some "rlp_content_to_u256_be_strict_at_guest_spec_within")
      (notes := "whole-routine `cpsTripleWithin (7 * len + 16)` over "
        ++ "`CodeReq.ofProg GuestAddrs.rlp_content_to_u256_be_strict "
        ++ "rlp_content_to_u256_be_strict_prog` (26 instructions, 0x80005418..0x8000547c). "
        ++ "⚠️ STATUS IS IN a0 HERE, not a1 as in the u64 helper one symbol back "
        ++ "(`li a0,0/3/2` at 0x80005468/0x80005470/0x80005478). ALL FOUR exit paths: "
        ++ "`32 < len` → a0=2; `len = 0` → a0=0 (ACCEPT); `0 < len ∧ content[0] = 0` → "
        ++ "a0=3; otherwise a0=0 and the buffer holds the right-aligned big-endian "
        ++ "u256. #12799 STRENGTHENED the two reject arms: the post now pins the "
        ++ "32 output bytes to ZERO on every path, because the four `sd zero,…(a2)` at "
        ++ "0x80005418..0x80005424 precede both the length check (0x8000542c) and the "
        ++ "leading-zero test (0x80005438). The previous post returned the buffer "
        ++ "merely owned on reject, which was strictly weaker than the code. Frameless "
        ++ "leaf, zero callees. Frame: writes a0 t0 t1 t2 t3 t4 (x10 x5 x6 x7 x28 x29) "
        ++ "plus the 32 bytes at a2; a1 and a2 are PRESERVED (no instruction writes "
        ++ "either); ra preserved. Loop back edge `j 0x8000544c` at 0x80005464, "
        ++ "decreasing on the t3/x28 counter. coverRef "
        ++ "`rlp_content_to_u256_be_strict_at_guest_instance` with negative control "
        ++ "`rlp_content_to_u256_be_strict_at_guest_negative_control`. Same #12686 "
        ++ "`guestImageEntries` caveat as the u64 row above"),

  -- #11925 continuation: `account_extract_nonce` is graded .conditional NOT
  -- .proven (unlike its sibling balance accessor) because the grade is
  -- INHERITED FROM ITS CALLEE, which is already registered .conditional above:
  -- `rlp_content_to_u64` (Routines.lean:204) carries the identical
  -- `a.nonce < 2 ^ 64` gate with the prose below, and the top-level triple
  -- repeats that exact hypothesis. Two structurally identical gates cannot
  -- carry different tiers. The satisfying instance is trivial: any `Account`
  -- whose nonce fits a u64 cell.
  routine "account_extract_nonce" .conditional
      (some "account_extract_nonce_spec_within")
      (gate := "`a.nonce < 2 ^ 64` — the accessor's u64 output width, narrower "
        ++ "than `Account.nonce`'s own `< 2 ^ 256` invariant")
      (notes := "grade inherited from its callee `rlp_content_to_u64`, which is "
        ++ "`.conditional` at Routines.lean:204 with this exact gate; every "
        ++ "dead code path carries a total post; step bound 139"),

  -- #11289: the RLP size / field / list routines whose specs `Correspondence`
  -- names but nothing witnessed. All whole-routine triples at their linked
  -- guest addresses (`B := GuestAddrs.<symbol>`), confirmed via the correspondence
  -- registry's `spec` refs. Tiers read per this module's header: only a
  -- nonvacuous input-domain gate is `.conditional`; buffer-slack, alignment,
  -- `isValidByteAccess`, register encoding and u64-representability are ABI.
  routine "rlp_bytes_encoded_size" .proven (some "rlpBytesEncodedSize_spec")
      (notes := "total: computes `rbesSize` for any byte payload whose length "
        ++ "matches the `len` register; only ABI hyps (ptr/len consistency, "
        ++ "alignment, validity)"),
  -- #11341: the same triple with its post restated over the SHARED MODEL
  -- (`EL.RLP.encodeBytes`) instead of the local `rbesSize`, via the bridge
  -- `rbesSize_eq_encodeBytes_length`. Both rows are kept: the machine-level
  -- theorem is still the thing proved, and this one is what makes the
  -- Correspondence row `.bridged` rather than `.machineOnly`.
  routine "rlp_bytes_encoded_size" .proven (some "rlpBytesEncodedSize_encode_spec")
      (notes := "model-facing restatement: `a0 = (EL.RLP.encodeBytes xs).length`. "
        ++ "One rewrite over `rlpBytesEncodedSize_spec`; the extra `hbound` is a "
        ++ "64-bit non-overflow guard on the register, an ABI hyp, not a domain gate"),
  routine "rlp_field_to_u64" .proven (some "rlpFieldToU64_spec_within")
      (notes := "companion to `rlp_field_to_u256_be` for the u64 field width"),
  -- The strict K34 wrapper is emitted as `rlp_field_to_u64_strict`.
  -- Its whole-routine proof lives under the shared SAsm namespace (the
  -- historical theorem name is `rlpFieldToU64_spec_within`), so bind the
  -- registry row explicitly to the emitted symbol rather than relying on
  -- theorem-name suffix matching.
  routine "rlp_field_to_u64_strict" .proven
      (some "EvmAsm.Codegen.RlpFieldToU64StrictSAsm.rlpFieldToU64_spec_within")
      (notes := "strict K34 wrapper; whole cpsTripleWithin over the emitted "
        ++ "`RlpFieldToU64StrictSAsm.code`; flat call-site adapter is "
        ++ "`rlpFieldToU64_flat_spec_within`. ABI bounds/alignment only"),
  routine "header_extract_logs_bloom" .proven
      (some "headerExtractLogsBloom_spec_within")
      (notes := "field-6 (`bloom`) extractor: prologue ;; `rlp_list_nth_item` at index 6 "
        ++ ";; a 256-byte copy loop ;; epilogue. Whole-routine triple predates its "
        ++ "correspondence row, like #11351's. Its step bound is DATA-DERIVED (the "
        ++ "`7 * 256` factor is the bloom copy), so unlike the numeric siblings it does "
        ++ "NOT inherit #11461's `7 * (2^64 - 1)` tail factor. Model tie "
        ++ "`header_logs_bloom_of_decode` is unconditional on the field width: #11615 "
        ++ "made the port perform the `FixedBytes` check the reference performs, so "
        ++ "`len = 256` is derived rather than assumed"),
  routine "header_validate_extra_data_length" .proven
      (some "header_validate_extra_data_length_spec_within")
      (notes := "field-12 (`extra_data`) length rule: prologue ;; `rlp_list_nth_item` at "
        ++ "index 12 ;; compare against 32 ;; epilogue. K20 only, so NO `7 * (2^64 - 1)` "
        ++ "factor -- #11461 does not reach this routine. ⚠️ Its model tie "
        ++ "`header_extra_data_length_of_decode` crosses a DIFFERENT comparison boundary "
        ++ "from the other header rows: `extra_data` is plain `Bytes` and unbounded at "
        ++ "decode time, so the <=32 rule is a `validate_header` clause "
        ++ "(SeamShell.lean:248), not a `_decode_header` field check. The tie is an IFF on "
        ++ "the decision, because the guest's a0=0/a0=1 guard is total over the field"),
  routine "headers_parent_hash" .proven (some "headers_parent_hash_spec_within")
      (notes := "Tier-A anchor (#12346): flat whole-routine triple (`cpsTripleWithin "
        ++ "312`) at `GuestAddrs.headers_parent_hash` over `CodeReq.ofProg hphBase "
        ++ "headersParentHash_prog` — the `GuestImageEntries` pairing itself, not a "
        ++ "structured-Spec caller union (#12390 error class: grade by the CodeReq, "
        ++ "not the name shape). RLP list-header parse of the parent header, 32-byte "
        ++ "hash copy to `GuestAddrs.hvph_claimed`; discharges the `nH` premise of "
        ++ "`header_validate_parent_hash` conjunct 11"),
  -- #12461 arm 11: unified whole-routine triple over the hvph caller itself.
  -- Rounds 1-3 of the 32-byte compare were covered by NO landed arm (match/
  -- mismatch0 only); a unified claim over those arms alone would have been
  -- FALSE on dword-1..3 inputs, so the MismatchLate chain lands WITH the unify.
  routine "header_validate_parent_hash" .proven
      (some "header_validate_parent_hash_spec_within")
      (notes := "⭐ #12799: PROMOTED from `.conditional` — the `hOutLen` gate is "
        ++ "GONE, not weakened. It read `(headersParentHash_out thisBytes "
        ++ "C0).length = 32` and claimed to exclude \"malformed inputs whose "
        ++ "extraction yields ≠ 32 bytes\"; there are none. "
        ++ "`headersParentHash_out_length` derives it from `hclaim0` alone: the "
        ++ "success branch's `take 32` is saturating because "
        ++ "`headersParentHash_ok` already demands `skip + 33 ≤ "
        ++ "thisBytes.length`, and the failure branch returns `C0` untouched. "
        ++ "So the premise restricted no input and the row now has NO gate. "
        ++ "coverRefs `header_validate_parent_hash_extract_fail_cover` / "
        ++ "`_match_cover` / `_mismatch2_cover` — one per arm, each "
        ++ "instantiating EVERY static premise at once with live data; all "
        ++ "three are now witness-abbrev'd (they were in no gate before). "
        ++ "Lemma non-vacuity: `hphSampleHeader_reaches_success` (success "
        ++ "branch reached) + `headersParentHash_out_length_refutable_without_"
        ++ "hclaimed` (negative control). "
        ++ "unified whole-routine triple over `fullCode` (hvph ∪ "
        ++ "headers_parent_hash ∪ zkvm_keccak256); 3-way post with no guards in "
        ++ "pre: status 0 all-4-dwords-equal `keccakBodyDigest` / 1 extract-fail "
        ++ "(leaf status ≠ 0) / 2 first-differing dword ∃ k < 4 — CLOSES the "
        ++ "rounds 1-3 gap. Single UPPER-BOUND cost `40 + 312 + nKeccak N rem` "
        ++ "(per-arm exact: 40+312+nK / 19+312 / 30+312+nK+3k). Covers "
        ++ "kernel-checked with LIVE data incl. the digest mutated at byte 16 "
        ++ "(dword 2) exercising the NEW arm. Adapter hcallee wiring = follow-up "
        ++ "owned by glm within 24h of merge: the adapter pre (`hvphEntryRest`) "
        ++ "must first be extended to own the Claimed cell + keccak Amb atoms "
        ++ "the callee writes"),
  -- #12346 K67: the post-merge header validation callee (difficulty = 0,
  -- nonce = 8 zero bytes, ommers = empty_ommers_hash).  Whole-routine triple
  -- over `fullCode` (post_merge ∪ rlp_walk_init ∪ rlp_walk_next) with the
  -- canonical guarded 5-way disjunctive post: every disjunct carries its
  -- static guard on the input bytes (k67GuardOk/Diff/Nonce/Ommers/Fail).
  routine "header_validate_post_merge" .proven
      (some "header_validate_post_merge_spec_within")
      (notes := "guarded 5-way post (`k67PostRet`): 0 clean 15-field walk + "
        ++ "nonce 8×0 + ommers = empty_ommers_hash / 1 field-7 len ≠ 0 / 2 "
        ++ "nonce rule violated / 3 ommers mismatch / 4 init-or-walk failure. "
        ++ "Static premises only: header-base 8-alignment, 0 < bytes.length, "
        ++ "overflow/byte-validity bounds, long-list implication gates, "
        ++ "aligned return address. Non-vacuity: "
        ++ "header_validate_post_merge_spec_within_inhabitable_long (concrete "
        ++ "production-shaped 0xf8/0x38 long-list full-premise instance at "
        ++ "RegionMap.inputRegion.base; the short-list inhabitant is also "
        ++ "available but is not the coverage citation)"),
  routine "header_extract_number" .proven (some "header_extract_number_spec_within")
      (notes := "8-instruction wrapper: prologue ;; `rlp_field_to_u64` at field index 8 "
        ++ ";; epilogue. The whole-routine triple predates the correspondence row "
        ++ "(#11351) -- a missing row was never evidence of a missing proof. Its step "
        ++ "bound inherits the callee's loose `7 * (2^64 - 1)` tail factor; tracked at "
        ++ "the origin as #11461"),
  -- #12313: three root extracts. Each already had a whole-program
  -- `cpsTripleWithin` at the guest base (`*_fnspec`); the allowlist called that
  -- "needs Fn.retSpecFlat", which is FALSE — no `Fn`/`retSpecFlat` appears in
  -- these files. The missing piece was CodeReq specialization (`*_spec_within`
  -- over wrapper ∪ walk_init ∪ walk_next). Residual INPUT-DOMAIN gate is
  -- `hbound` (every walked `rlpItemDecode` has 32 bytes of content room).
  routine "header_extract_state_root" .conditional
      (some "header_extract_state_root_spec_within")
      (gate := "`hbound`: ∀ walked `rlpItemDecode` of the header list, the decoded "
        ++ "content has room for 32 bytes (`(next-len-listBase).toNat + 32 ≤ "
        ++ "|headerBytes|`). ABI hyps (`align`, `slack`, `valid`, `dst≥32`) are "
        ++ "not domain gates. coverRef: any well-formed header whose field-3 "
        ++ "payload is a 32-byte string")
      (notes := "flat guest-image specialization of `header_extract_state_root_fnspec` "
        ++ "(field 3 = walk_init + 4×walk_next + 32-byte LBU/SB copy). Allowlist "
        ++ "tier-B / retSpecFlat note drained — it named a combinator that does "
        ++ "not appear in HeaderFieldsSpec (#12313 / #11637 mislabel)"),
  routine "header_extract_receipts_root" .conditional
      (some "header_extract_receipts_root_spec_within")
      (gate := "`hbound`: ∀ walked `rlpItemDecode` of the header list, the decoded "
        ++ "content has room for 32 bytes (`(next-len-listBase).toNat + 32 ≤ "
        ++ "|headerBytes|`). Same gate shape as `header_extract_state_root`")
      (notes := "flat guest-image specialization of `header_extract_receipts_root_fnspec` "
        ++ "(field 5 = walk_init + 6×walk_next). Same CodeReq specialization as "
        ++ "state_root; allowlist retSpecFlat note drained (#12313)"),
  routine "header_extract_withdrawals_root" .conditional
      (some "header_extract_withdrawals_root_spec_within")
      (gate := "`hbound`: ∀ walked `rlpItemDecode` of the header list, the decoded "
        ++ "content has room for 32 bytes (`(next-len-listBase).toNat + 32 ≤ "
        ++ "|headerBytes|`). Same gate shape as `header_extract_state_root`")
      (notes := "flat guest-image specialization of `header_extract_withdrawals_root_fnspec` "
        ++ "(field 16 = walk_init + 17×walk_next). Same CodeReq specialization as "
        ++ "state_root; allowlist retSpecFlat note drained (#12313)"),
  -- #12275: production decoder direct u64 segments. These rows share one
  -- generic caller-segment theorem; the field is determined by the call site.
  -- #12345. SpecRef-shaped `validate_header` re-emit (SeamShell.validate_header
  -- conjunct order). Whole-routine correspondence triple is #12346; until then
  -- the honest tier is `.partly` — the emission + byte-tie exist, no Hoare triple.
  routine "validate_header" .partly
      (some "validateHeaderFunction_eq_prog")
      (notes := "SpecRef.validate_header mirror at GuestAddrs.validate_header: number<1, "
        ++ "excess blob gas, gas_used≤limit, base-fee (incl. check_gas_limit), timestamp>parent, "
        ++ "number=parent+1, extra_data≤32, post-merge trio, parentHash=headerHash(parent). "
        ++ "Replaces retired validate_header_full at the validate_header_rlp_pair site. "
        ++ "Witness is the emit drift guard only; cpsTripleWithin is #12346"),
  -- #12799. These five rows previously ALL cited the same theorem,
  -- `header_extended_decode_u64_segment_spec_within` — a 3-instruction
  -- contract over a universally quantified base `A`, a FREE `CodeReq`
  -- variable `cr` constrained only by three singleton memberships, and an
  -- ASSUMED callee (`hcallee` was a hypothesis). Five `.proven` rows on a
  -- 174-instruction production routine rested on that. They now cite one
  -- anchored per-site corollary each: `A` is the site's real address in the
  -- linked image, `cr` is `headerExtendedDecodeU64Code` (decoder image ∪
  -- callee image), and the callee's four-arm whole-routine contract is
  -- COMPOSED from `EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_spec_within`
  -- rather than assumed. Still only the 3-instruction call segments: the
  -- 174-instruction whole-decoder triple is #12799 ownership row 6.
  --
  -- ⚠️ TWO DISCREPANCIES DELIBERATELY LEFT FOR THE MAINTAINER, not fixed here:
  --  (1) There are SIX direct `rlp_content_to_u64_strict` sites (+324, +364,
  --      +404, +444, +604, +644) and five rows. `+444` now has a theorem
  --      (`header_extended_decode_u64_site_444_spec_within`) and no row.
  --  (2) The field labels below are off by one site for the first three. The
  --      outward-call census `example` in
  --      `EvmAsm/Codegen/Programs/HeaderU64ExtractSpec.lean` is `decide`-checked
  --      and pins every `JAL x1` index in the Program; the decoder reaches
  --      field `i` via `rlp_walk_init` + `i+1` × `rlp_walk_next`, so counting
  --      gives +324→8 `number`, +364→9 `gas_limit`, +404→10 `gas_used`,
  --      +444→11 `timestamp`, +604→17, +644→18. That agrees with this file's
  --      own source docstring ("fields 8, 9, 10, 11, 17 and 18") and with the
  --      two anchors both sources already agree on (+548 u256 = field 15, and
  --      +604/+644 = 17/18). Renaming four rows is a registry call, so the
  --      notes below are marked rather than rewritten.
  routine "header_extended_decode" .proven
      (some "header_extended_decode_u64_site_324_spec_within")
      (notes := "direct u64 segment at +324, anchored at "
        ++ "GuestAddrs.header_extended_decode + 316 over the decoder∪callee "
        ++ "CodeReq, callee composed (not assumed). Result stored at out+64. "
        ++ "⚠️ field label: this row says 9 (`gas_limit`); the decide-checked "
        ++ "call census says field 8 (`number`) — see #12799"),
  routine "header_extended_decode" .proven
      (some "header_extended_decode_u64_site_364_spec_within")
      (notes := "direct u64 segment at +364, anchored at "
        ++ "GuestAddrs.header_extended_decode + 356, callee composed. Result "
        ++ "stored at out+80. ⚠️ field label: this row says 10 (`gas_used`); "
        ++ "the census says field 9 (`gas_limit`) — see #12799"),
  routine "header_extended_decode" .proven
      (some "header_extended_decode_u64_site_404_spec_within")
      (notes := "direct u64 segment at +404, anchored at "
        ++ "GuestAddrs.header_extended_decode + 396, callee composed. Result "
        ++ "stored at out+88. ⚠️ field label: this row says 11 (`timestamp`); "
        ++ "the census says field 10 (`gas_used`) — see #12799"),
  routine "header_extended_decode" .proven
      (some "header_extended_decode_u64_site_604_spec_within")
      (notes := "field 17 (`blob_gas_used`), direct u64 segment at +604, "
        ++ "anchored at GuestAddrs.header_extended_decode + 596, callee "
        ++ "composed. Result stored at out+128. Field label agreed by both "
        ++ "sources and by the call census"),
  routine "header_extended_decode" .proven
      (some "header_extended_decode_u64_site_644_spec_within")
      (notes := "field 18 (`excess_blob_gas`), direct u64 segment at +644, "
        ++ "anchored at GuestAddrs.header_extended_decode + 636, callee "
        ++ "composed. Result stored at out+136. Field label agreed by both "
        ++ "sources and by the call census"),
  -- #12799 ownership-table row 5, PARTIAL.  Extent re-derived from `nm` +
  -- next symbol (`GuestAddrs.header_extended_decode_arity_check` ->
  -- `GuestAddrs.headers_parent_hash`, 468 B) and cross-checked against
  -- `headerExtendedDecodeArityCheck_prog.length * 4 = 117 * 4 = 468`
  -- (`HeaderArityCheckTie.arity_length` / `arity_extent`).  The issue body's
  -- "194" spans THREE symbols; 117 is the routine.
  --
  -- ⛔ There is NO whole-routine triple for this symbol.  These three rows are
  -- the shared-exit, length-arm and dispatch contracts only; the prologue, the
  -- two callee arms and the loop are NOT covered.  See the module docstring.
  routine "header_extended_decode_arity_check" .proven
      (some "epilogue_spec_within")
      (notes := "SHARED EXIT, the 34-branch fan-in factored. `cpsTripleWithin "
        ++ "10` at `GuestAddrs.header_extended_decode_arity_check + 428` over "
        ++ "`CodeReq.ofProg L headerExtendedDecodeArityCheck_prog` — reload "
        ++ "`s6,s5,s4,s3,s2,s1,s0,ra`, close the 96-byte frame, `ret`. Proved "
        ++ "ONCE and instantiated TWICE: `fail_exit_spec_within` (+424, `a0:=1`, "
        ++ "the target of ALL TEN failure branches at +60/+80/+104/+128/+324/"
        ++ "+336/+348/+360/+380/+404) and `ok_exit_spec_within` (+416, `a0:=0`, "
        ++ "the single success branch at +112). Every pinned register is read "
        ++ "off its own `sd`/`ld` line; the frame table is in the module "
        ++ "docstring. coverRef `fail_exit_instance` + `ok_exit_instance` (same "
        ++ "17 frame arguments, different `a0` — the shared epilogue did not "
        ++ "collapse the two exits); negative control "
        ++ "`arity_premises_refutable`. No gate: no callee is reached from the "
        ++ "epilogue. Lives in `Codegen/Programs/HeaderArityCheckTie.lean`"),
  routine "header_extended_decode_arity_check" .proven
      (some "len_check_arm_within")
      (notes := "THE FOUR LENGTH ARMS, one lemma. `cpsBranchWithin 3` from an "
        ++ "arm entry `A` to `+424` (FAIL, reported content length ≠ K) or "
        ++ "`+408` (the loop join). Instantiated four times — "
        ++ "`len_arm_32_within` (+320, K=32), `len_arm_20_within` (+332, K=20), "
        ++ "`len_arm_256_within` (+344, K=256), `len_arm_8_within` (+356, K=8) "
        ++ "— each discharging its three code lookups as kernel-checked `rfl`s, "
        ++ "twelve in all, and proving nothing new. No gate. coverRef the four "
        ++ "`len_arm_*_within` (each closed but for `a2`); negative control "
        ++ "`arity_premises_refutable` conjuncts 1 and 2, which refute the `hbt` "
        ++ "target and the `hli` lookup instantiated the WRONG way"),
  routine "header_extended_decode_arity_check" .proven
      (some "dispatch_spec_within")
      (notes := "THE 22-PROBE DISPATCH, `cpsTripleWithin 45` from `+140` to "
        ++ "`dispatchTarget s5` — a SINGLE-exit triple whose exit PC is a "
        ++ "computed function of the loop index, so there is no 23-way case "
        ++ "split anywhere. Built from one two-instruction lemma "
        ++ "(`dispatch_probe_within`, `li t0,K` ⨾ `beq s5,t0,T`) chained by "
        ++ "`dispatch_step`, whose `by_cases` on `i = K` is the only case "
        ++ "analysis and is proved once. 22 instantiations, 44 `rfl`-discharged "
        ++ "code lookups. No gate. coverRef `dispatch_instance_6` (field 6 -> "
        ++ "+344) + `dispatch_instance_12` (the one index in 0..22 no probe "
        ++ "names, so all 22 probes run and the 45-step bound is reached) + "
        ++ "`dispatchTarget_values`; negative control `arity_premises_refutable` "
        ++ "conjuncts 3 and 4. ⭐ The dispatch and the arms are shown to MEET, "
        ++ "not merely to coexist: `dispatch_then_arm_within` composes them into "
        ++ "a `cpsBranchWithin 48` over `+140 .. +328` whose taken exit is the "
        ++ "shared `+424` stub, closed at `dispatch_then_arm_6` and "
        ++ "`dispatch_then_arm_0`"),
  routine "header_extended_decode_arity_check" .proven
      (some "arity_gate_within")
      (notes := "THE NAMESAKE CHECK. `cpsBranchWithin 4` at "
        ++ "`GuestAddrs.header_extended_decode_arity_check + 92` (prog idx "
        ++ "23..26): the RLP item count `s4` must be 21 (pre-Cancun) or 23 "
        ++ "(with the two blob fields), else the shared `+424` stub. Both "
        ++ "accepting branches converge on `+108`, the loop entry; the "
        ++ "rejecting post records `n ≠ 23` only, since `n ≠ 21` is true there "
        ++ "but read by nothing. No gate — no callee is reached. Composed from "
        ++ "the two `li`/compare blocks by `cpsBranchWithin_seq_cpsBranchWithin_"
        ++ "same_cr` with the second swapped, so the two accepting exits meet "
        ++ "without a case split"),
  routine "header_extended_decode_arity_check" .proven
      (some "loop_backedge_within")
      (notes := "LOOP CONTROL SKELETON — termination only. "
        ++ "`loop_guard_within` (`cpsBranchWithin 1` at `+112`, prog idx 28: "
        ++ "leave to `+416` when `s5 = s4`, else enter the body at `+116`), "
        ++ "`loop_backedge_within` (`cpsTripleWithin 2` at `+408`, prog idx "
        ++ "102..103 — `addi s5,s5,1` then the routine's ONLY backward "
        ++ "transfer, `j +112`; nothing else in the body writes `s5`), and "
        ++ "`loop_measure_decreases` (`(s4 - s5 : Nat)` strictly decreases, "
        ++ "with no extra no-wrap premise: `s5 < s4 ≤ 2^64 - 1` already forbids "
        ++ "the increment from wrapping). ⛔ This settles TERMINATION and NOT "
        ++ "the invariant: closing the loop still needs "
        ++ "`rlp_walk_next_leaf`'s entry premises re-established for iteration "
        ++ "i+1 from the `rlpItemDecodeStrictW` post of iteration i, a "
        ++ "derivation that exists at no level of the stack (#12835 named the "
        ++ "same blocker for row 6, where the sites are straight-line and can "
        ++ "be rowed one at a time; here they are one site under a loop, so "
        ++ "there is no per-site fallback). No gate on these three"),
  -- #12799 ownership row 6, PART of it. ⚠️ These two rows are NOT a
  -- whole-routine triple for the 174-instruction decoder. They cover two of
  -- its four internal layers:
  --
  --   * the two 32-byte field-copy loops (one lemma, both sites), and
  --   * the nineteen `rlp_walk_next` call sites (callee composed).
  --
  -- What row 6 still owns after these: chaining the nineteen sites (each
  -- site's cursor is the previous site's `a0`, described only through
  -- `rlpItemDecodeStrictW`, so site i+1's `WalkPre` has to be DERIVED from
  -- site i's post — that derivation does not exist yet), the prologue's
  -- `rlp_walk_init` call, the status branches, and the shared epilogue.
  --
  -- Extent re-derived rather than taken from prose: `nm` on
  -- `gen-out/regionmap/stateless_guest.elf` gives
  -- `0x8000bb64 → 0x8000be1c` = 696 B, and
  -- `headerExtendedDecode_prog_length = 174`; 174 * 4 = 696. ✅
  routine "header_extended_decode" .proven
      (some "parent_hash_copy_spec_within")
      (notes := "the two 32-byte field-copy loops, ONE lemma applied twice. "
        ++ "The loops at GuestAddrs.header_extended_decode + 88 (program "
        ++ "indices 22..27, parent_hash → out+0) and + 192 (indices 48..53, "
        ++ "state_root → out+32) are byte-identical; "
        ++ "HeaderExtendedDecodeCopy.copy_loop_spec_within is proved once and "
        ++ "instantiated at both, the twelve code memberships `rfl`-checked "
        ++ "against headerExtendedDecode_prog. Sibling: "
        ++ "state_root_copy_spec_within. Anchored over "
        ++ "CodeReq.ofProg GuestAddrs.header_extended_decode "
        ++ "headerExtendedDecode_prog — no free base, no free CodeReq. "
        ++ "Step bound 6*(n+1). Premises are alignment / in-bounds / "
        ++ "valid-byte-access / no-wrap only, i.e. resource framing, hence "
        ++ ".proven; source and destination are separate bytesRegion atoms, "
        ++ "so the non-overlapping case is what is covered — which is what "
        ++ "the decoder does (RLP input buffer → caller's output struct). "
        ++ "Follows the #12813 factoring precedent for five identical copy "
        ++ "loops. Non-vacuity: parent_hash_copy_instance, "
        ++ "state_root_copy_instance, parent_hash_copy_content (the POST is "
        ++ "non-vacuous too), copy_loop_hyps_refutable"),
  routine "header_extended_decode" .proven
      (some "walk_init_site_spec_within")
      (notes := "the ONE rlp_walk_init call site, at "
        ++ "GuestAddrs.header_extended_decode + 32 (program index 8), opening "
        ++ "the header list. 82 steps = 1 + the callee's 81. Callee COMPOSED "
        ++ "from RlpWalkInitTie.rlp_walk_init_entry_spec_within, which is "
        ++ ".proven and carries NO gate — so this site adds nothing to the "
        ++ "decoder's gate; the whole gate comes from the nineteen "
        ++ "rlp_walk_next sites. Six-way status post preserved verbatim. "
        ++ "CodeReq is initSiteCode = decoder image ∪ rlp_walk_init image, "
        ++ "disjointness derived from the two GuestAddrs extents. "
        ++ "Non-vacuity: walk_init_site_instance on the same sampleList the "
        ++ "callee's own instance uses; the premises' negative control is "
        ++ "RlpWalkInitTie.rlp_walk_init_entry_hyps_refutable"),
  routine "header_extended_decode" .conditional
      (some "walk_next_site_composed_within")
      (gate := "The RLP prefix byte at the walk cursor is < 0xc0 (the item is "
        ++ "a byte string, not a LIST): WalkPre.notlist. INHERITED unchanged "
        ++ "from row 3 of #12799 "
        ++ "(RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within) "
        ++ "and NOT discharged here — no instruction of header_extended_decode "
        ++ "inspects the prefix byte before the call (the only post-call test "
        ++ "is `bnez a1` on the returned status), so the routine cannot "
        ++ "establish it; it is a property of the caller's input buffer. Every "
        ++ "header field IS a byte string, so the non-LIST arm is the live one "
        ++ "on well-formed input — but this is a decoder, reachable with "
        ++ "arbitrary attacker-supplied bytes, so that is not a proof. "
        ++ "The gate SURVIVES into anything built on these rows; #12776 "
        ++ "inherits it downstream. WalkPre's other nine fields (alignment, "
        ++ "in-bounds, no-wrap, valid byte access, the three prefix-class "
        ++ "continuation obligations, and the cursor < endPtr translation of "
        ++ "the thunk's s0 ≥ 2 budget) are resource framing.")
      (notes := "the nineteen rlp_walk_next call sites at "
        ++ "GuestAddrs.header_extended_decode + 56, 120, 140, 160, 224, 244, "
        ++ "264, 284, 304, 344, 384, 424, 464, 484, 504, 524, 564, 584, 624. "
        ++ "Each is `mv a0,s3 ; mv a1,s1 ; jal rlp_walk_next` at <off> - 8, "
        ++ "125 steps = 2 + 1 + the thunk's 122. The callee's whole-routine "
        ++ "contract is COMPOSED via cpsCallWithin, not assumed. Nineteen "
        ++ "anchored corollaries walk_next_site_{56,…,624}_spec_within, three "
        ++ "`rfl` code memberships each against headerExtendedDecode_prog. "
        ++ "CodeReq is walkSiteCode = decoder image ∪ thunk ∪ "
        ++ "rlp_walk_next_shared ∪ rlp_walk_next_core, disjointness derived "
        ++ "from the four linked extents. Non-vacuity: walkPre_instance, "
        ++ "walk_next_site_56_instance, and TWO negative controls — "
        ++ "walkPre_refutable_on_list (the gate is provably FALSE on a 0xc0 "
        ++ "prefix, so it excludes real inputs) and "
        ++ "walkPre_refutable_on_empty_span"),
  -- #11575, tier A. Both triples ALREADY EXISTED, sorry-free, and were named in
  -- `scripts/registry-coverage-allow.txt` as "registrable as .proven, not yet
  -- rowed" -- the #11637 row-existence class, where proven work counts toward
  -- nothing. #11351's note applies verbatim: a missing row was never evidence of
  -- a missing proof. Registering them here drains those two allowlist entries.
  --
  -- Graded `.proven`, not `.conditional`: every hypothesis is resource/ABI --
  -- `hspC` (frame base), `hret` (ret alignment), `hnWord` (definitional),
  -- `hN : lengths.length < 2 ^ 64`, and the six `hAll*` per-header alignment /
  -- length / slack / non-overflow / `isValidByteAccess` facts. Per this module's
  -- header those are the ABI, not a gap. There is NO input-domain gate: the
  -- three-way post is total over the header list.
  -- Graded `.proven`, not `.conditional`: identical shape to the two twins above
  -- (same frame, hypothesis set and three-way total post), just a `< limit` upper
  -- bound on the `gas_used` field instead of a `+1`/strict-increase step. Both
  -- twins were graded `.proven`; this triple is a DIRECT `cpsTripleWithin`,
  -- structurally identical to `chain_validate_consecutive_numbers` (no
  -- `Fn`/`Fn.retSpecFlat`), so grading it tier B on the allowlist would put two
  -- structurally identical triples at different grades. Every hypothesis is
  -- resource/ABI (`hspC` frame base, `hret` ret alignment, `hnWord` definitional,
  -- `hN : lengths.length < 2 ^ 64`, and the six `hAll*` per-header facts); there
  -- is NO input-domain gate, the post is total over the header list. Former allowlist
  -- entry drained (#11575). No `Correspondence` row yet -- same missing
  -- `_of_decode` bridge as the twins.
  -- #12386: the four standalone chain validators are retired from the guest
  -- image and drained from this registry; their predicates are enforced by
  -- reachable header/body validators and their Program proofs remain offline.

  -- #11925 continuation: the first registrations out of scripts/proof-frontier.py's
  -- present-but-unrowed bucket (the #11637 row-existence debt). All four are direct
  -- whole-routine `cpsTripleWithin` triples found live by the frontier census; the
  -- `hbound`-style hypotheses each carries are STATIC input well-formedness / slack
  -- facts tied to the decode predicates, not runtime-outcome gates — the posts stay
  -- total disjunctions that still state the failure branches. Graded `.proven`.
  routine "account_decode" .proven (some "account_decode_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.account_decode`: decodes the "
        ++ "RLP account record (balance/root/codeHash) to `a0 = 0` with a total "
        ++ "whole-routine post `adWholePost`. Every hypothesis is ABI/resource "
        ++ "(`hspW` frame base, `hret` ret alignment, `hlenW` definitional, and "
        ++ "align/slack/over/valid for the input region plus the three output cells). "
        ++ "No input-domain gate"),
  routine "account_extract_balance" .proven (some "account_extract_balance_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.account_extract_balance`: writes "
        ++ "`word256Bytes32 a.balance` and returns `a0 = 0`. Its callee "
        ++ "`rlp_content_to_u256_be` is itself `.proven` (Routines.lean:207), and its "
        ++ "only value-shaped hypothesis is `hnonce : a.nonce < 2 ^ 256` — the "
        ++ "NATURAL `Word256` bound, not a restriction (identical to the u256 callee's "
        ++ "own hypothesis). All other hyps are ABI/resource. No input-domain gate"),
  routine "account_is_eip161_empty" .proven (some "account_is_eip161_empty_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.account_is_eip161_empty`: the post "
        ++ "`aieOutcome` is a TOTAL 4-way disjunction on `(a0, outVal)` — "
        ++ "`accountEip161Empty` verdict, non-empty verdict, and two error statuses. "
        ++ "EIP-161 empty-ness is the OUTPUT the routine verifies, not a precondition. "
        ++ "Hyps are ABI/resource plus a static slack hypothesis over the RLP decode "
        ++ "predicate. No input-domain gate; axiom-clean confirmed via lean_verify"),
  routine "receipt_extract_logs_bloom" .proven (some "receiptExtractLogsBloom_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.receipt_extract_logs_bloom`: the "
        ++ "post `relbRetPost` is a TOTAL 3-way disjunction — success with the 256-byte "
        ++ "bloom copied, success with a short/long payload left intact, and the RLP "
        ++ "decode-failure arm. `hbound` is a static slack fact keyed on the input's "
        ++ "`Success` decode predicate (so the COPY target is in range), not a runtime "
        ++ "outcome gate — the failure branch is still stated. ABI/resource hyps only; "
        ++ "calls RlpFieldToU64SAsm.code"),

  routine "rlp_list_encoded_size" .proven (some "rlpListEncodedSize_spec")
      (notes := "total: the result covers BOTH the `ult v 56` short branch and "
        ++ "the long branch, so it is not form-gated — the only hyp is `halignRet`"),
  -- #11341: the same triple restated over the SHARED MODEL
  -- (`(EL.RLP.encode (.list items)).length`) via `rlesSize_eq_encode_list_length`.
  -- The machine row above states its formula INLINE and unnamed; `rlesSize` in the
  -- bridge module names it (definitionally the same), which is what made the
  -- comparison statable at all.
  routine "rlp_list_encoded_size" .proven (some "rlpListEncodedSize_encode_spec")
      (notes := "model-facing restatement: `a0 = (EL.RLP.encode (.list items)).length` "
        ++ "for any item list whose encoded payload is `a0` bytes long. One rewrite "
        ++ "over `rlpListEncodedSize_spec`; `hbound` is 64-bit non-overflow, an ABI hyp"),
  routine "rlp_list_nth_item" .proven (some "rlpListNthItem_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.rlp_list_nth_item`; the "
        ++ "consumer of the account decode / apply paths"),
  routine "rlp_list_count_items" .proven (some "rlp_list_count_items_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.rlp_list_count_items`"),
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_short_pinned_spec_within")
      (gate := "`len.toNat < 56` — the RLP short-form list-prefix bound. The "
        ++ "`lenlen ≥ 2` long forms are the documented cut (#10780 item 3), the "
        ++ "same boundary as `rlp_item_size`")
      (notes := "per-form (\"short\") pinned triple; writes header byte "
        ++ "`0xC0 + len` and sets the cell flag to 1"),
  -- #10780: the 1-length-byte long form was proven in `RlpSpliceHelperSpec.lean`
  -- but never registered, so it was outside the axiom gate and the registry
  -- undercounted the routine's coverage — the short row's own gate text already
  -- describes the cut as `lenlen ≥ 2`, which only makes sense if lenlen = 1 is
  -- done. Same situation as the #11291 note below: the triple existed, the row
  -- did not. Registering existing work; no new proof.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long1_pinned_spec_within")
      (gate := "`56 ≤ len.toNat < 256` — the 1-length-byte long form. Together "
        ++ "with the short row this covers `len < 256`; `lenlen ≥ 2` (the "
        ++ "`SLLI`-widened arms) remains the cut, #10780 item 3")
      (notes := "per-form (\"long1\") pinned triple; writes header bytes "
        ++ "`[0xF8, len]` and sets the cell flag to 2. Length-of-length is one "
        ++ "byte and minimal by construction here, so no leading-zero side "
        ++ "condition is needed at this width"),
  -- #10780 item 3: the first arm where the length-byte loop runs MORE THAN ONCE, and
  -- the first where canonical form is a real obligation rather than vacuous.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long2_pinned_spec_within")
      (gate := "`256 ≤ len.toNat < 65536` — the 2-length-byte long form. With the "
        ++ "short and long1 rows this covers `len < 65536`; `lenlen ≥ 3` remains "
        ++ "the cut")
      (notes := "per-form (\"long2\") pinned triple; writes `[0xF9, len >>> 8, len]` "
        ++ "and sets the cell flag to 3. The length-byte loop runs TWICE here, so "
        ++ "the step bound is 32 rather than long1's 22. ⭐ Canonical form is "
        ++ "discharged separately by `long2_first_length_byte_ne_zero`: the high "
        ++ "byte is nonzero, so the length-of-length carries no leading zero — "
        ++ "vacuous at long1, real from here on"),
  -- #10780 item 3: the first arm that CITES the length-byte loop instead of
  -- unrolling it. `lpLolLoop` (RlpEncodeListPrefixLoopSpec) proves idx35-idx41 at
  -- a symbolic trip count, so this arm is its ladder path plus the fixed
  -- header/epilogue -- which is why it costs 580 lines rather than the ~200/byte
  -- the long2 header priced unrolling at.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long3_pinned_spec_within")
      (gate := "`65536 ≤ len.toNat < 16777216` — the 3-length-byte long form. With "
        ++ "the short, long1 and long2 rows this covers `len < 16777216`; the cut "
        ++ "moves to `lenlen ≥ 4`")
      (notes := "per-form (\"long3\") pinned triple; writes "
        ++ "`[0xFA, len >>> 16, len >>> 8, len]` and sets the cell flag to 4. Step "
        ++ "bound 42 = 11 ladder + 5 header + 22 loop (`7*3+1`) + 3 epilogue + 1 "
        ++ "`JALR`. ⭐ The loop is CITED, not unrolled: `lpLolLoop` covers "
        ++ "idx35-idx41 at any trip count `≤ 8`, so each further width is its "
        ++ "ladder path plus this same epilogue. Canonical form comes from the "
        ++ "all-widths `first_length_byte_ne_zero`, specialised here as "
        ++ "`long3_first_length_byte_ne_zero`"),
  -- #10780 item 3, next width: long3's ladder with ONE more fall-through. The only
  -- two differences from long3 are the extra dispatch triple (idx17-idx19) and the
  -- loop citation at `m := 4`; header writer, epilogue, frame and clobber set are
  -- identical, which is what long3's closing note predicted.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long4_pinned_spec_within")
      (gate := "`16777216 ≤ len.toNat < 4294967296` — the 4-length-byte long form. "
        ++ "With the short, long1, long2 and long3 rows this covers "
        ++ "`len < 4294967296`; the cut moved to `lenlen ≥ 5`, which the long5, "
        ++ "long6 and long7 rows below then push to `lenlen ≥ 8`. ⚠️ INPUT-DOMAIN gate "
        ++ "ONLY: `h_out_align`, `h_out_len` and `h_out_valid` are ABI obligations "
        ++ "on the caller-supplied output region, not domain restrictions. coverRef "
        ++ "is the smallest qualifying input, `len = 16777216` — exactly the "
        ++ "long3/long4 boundary, so the gate is REACHABLE and adjacent to already "
        ++ "covered ground rather than merely consistent (#12014)")
      (notes := "per-form (\"long4\") pinned triple; writes "
        ++ "`[0xFB, len >>> 24, len >>> 16, len >>> 8, len]` and sets the cell flag "
        ++ "to 5. Step bound 52 = 14 ladder + 5 header + 29 loop (`7*4+1`) + 3 "
        ++ "epilogue + 1 `JALR` — long3's 42 with three more dispatch steps and "
        ++ "seven more loop steps. ⭐ The loop is CITED at `m := 4`, not unrolled. "
        ++ "Canonical form comes from the all-widths `first_length_byte_ne_zero`, "
        ++ "specialised here as `long4_first_length_byte_ne_zero`. The loop's "
        ++ "overflow side condition is `outPtr.toNat + 5 ≤ 2^64`, which still "
        ++ "closes from `outPtr.toNat % 8 = 0` alone"),
  -- #10780 item 3, widths 5/6/7/8. Each row is long4's arm with ONE more ladder
  -- fall-through and the loop cited one trip longer; header writer (idx30-34),
  -- epilogue (idx42-44), frame and clobber set are byte-identical across the
  -- family, so the per-width cost really is the three dispatch steps long4
  -- measured. Width 8 needs an explicit room bound (`outPtr+9 ≤ 2^64` from
  -- validity) rather than alignment alone — see the long8 row.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long5_pinned_spec_within")
      (gate := "`4294967296 ≤ len.toNat < 1099511627776` — the 5-length-byte long "
        ++ "form. With the short, long1, long2, long3 and long4 rows this covers "
        ++ "`len < 1099511627776`; the cut moves to `lenlen ≥ 6`. ⚠️ INPUT-DOMAIN "
        ++ "gate ONLY: `h_out_align`, `h_out_len` and `h_out_valid` are ABI "
        ++ "obligations on the caller-supplied output region, not domain "
        ++ "restrictions. coverRef is the smallest qualifying input, "
        ++ "`len = 4294967296` — exactly the long4/long5 boundary, so the gate is "
        ++ "REACHABLE and adjacent to already covered ground rather than merely "
        ++ "consistent (#12014)")
      (notes := "per-form (\"long5\") pinned triple; writes "
        ++ "`[0xFC, len >>> 32, len >>> 24, len >>> 16, len >>> 8, len]` and sets "
        ++ "the cell flag to 6. Step bound 62 = 17 ladder (idx 0, 1, 8-22) + 5 "
        ++ "header + 36 loop (`7*5+1`) + 3 epilogue + 1 `JALR` — long4's 52 with "
        ++ "three more dispatch steps and seven more loop steps. ⭐ The loop is "
        ++ "CITED at `m := 5`, not unrolled. Canonical form comes from the "
        ++ "all-widths `first_length_byte_ne_zero`, specialised here as "
        ++ "`long5_first_length_byte_ne_zero`. The loop's overflow side condition "
        ++ "is `outPtr.toNat + 6 ≤ 2^64`, which still closes from "
        ++ "`outPtr.toNat % 8 = 0` alone"),
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long6_pinned_spec_within")
      (gate := "`1099511627776 ≤ len.toNat < 281474976710656` — the 6-length-byte "
        ++ "long form. With the short and long1-long5 rows this covers "
        ++ "`len < 281474976710656`; the cut moves to `lenlen ≥ 7`. ⚠️ INPUT-DOMAIN "
        ++ "gate ONLY: `h_out_align`, `h_out_len` and `h_out_valid` are ABI "
        ++ "obligations on the caller-supplied output region, not domain "
        ++ "restrictions. coverRef is the smallest qualifying input, "
        ++ "`len = 1099511627776` — exactly the long5/long6 boundary, so the gate "
        ++ "is REACHABLE and adjacent to already covered ground rather than merely "
        ++ "consistent (#12014)")
      (notes := "per-form (\"long6\") pinned triple; writes "
        ++ "`[0xFD, len >>> 40, len >>> 32, len >>> 24, len >>> 16, len >>> 8, "
        ++ "len]` and sets the cell flag to 7. Step bound 72 = 20 ladder "
        ++ "(idx 0, 1, 8-25) + 5 header + 43 loop (`7*6+1`) + 3 epilogue + 1 "
        ++ "`JALR`. ⭐ The loop is CITED at `m := 6`, not unrolled. Canonical form "
        ++ "comes from the all-widths `first_length_byte_ne_zero`, specialised "
        ++ "here as `long6_first_length_byte_ne_zero`. The loop's overflow side "
        ++ "condition is `outPtr.toNat + 7 ≤ 2^64`, which still closes from "
        ++ "`outPtr.toNat % 8 = 0` alone"),
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long7_pinned_spec_within")
      (gate := "`281474976710656 ≤ len.toNat < 72057594037927936` — the "
        ++ "7-length-byte long form. With the short and long1-long6 rows this "
        ++ "covers `len < 72057594037927936`; the cut moves to `lenlen = 8` "
        ++ "(long8). ⚠️ INPUT-DOMAIN gate ONLY: `h_out_align`, `h_out_len` and "
        ++ "`h_out_valid` are ABI obligations on the caller-supplied output "
        ++ "region, not domain restrictions. coverRef is the smallest qualifying "
        ++ "input, `len = 281474976710656` — exactly the long6/long7 boundary, so "
        ++ "the gate is REACHABLE and adjacent to already covered ground rather "
        ++ "than merely consistent (#12014)")
      (notes := "per-form (\"long7\") pinned triple; writes "
        ++ "`[0xFE, len >>> 48, …, len >>> 8, len]` and sets the cell flag to 8. "
        ++ "Step bound 82 = 23 ladder (idx 0, 1, 8-28) + 5 header + 50 loop "
        ++ "(`7*7+1`) + 3 epilogue + 1 `JALR`. ⭐ The loop is CITED at `m := 7`, "
        ++ "not unrolled. Canonical form comes from the all-widths "
        ++ "`first_length_byte_ne_zero`, specialised here as "
        ++ "`long7_first_length_byte_ne_zero`. Alignment alone closes "
        ++ "`outPtr.toNat + 8 ≤ 2^64`; `+ 9` (long8) needs an explicit room "
        ++ "bound from validity — see the long8 row"),
  -- #10780 / #12038: width-8 arm. Triple + axiom witness existed on main but
  -- had no registry row — the coverage gate is per-symbol, so eight prior rows
  -- already "covered" `rlp_encode_list_prefix` while long8 stayed unrowed.
  routine "rlp_encode_list_prefix" .conditional
      (some "rlp_encode_list_prefix_long8_pinned_spec_within")
      (gate := "`72057594037927936 ≤ len.toNat` — the 8-length-byte long form "
        ++ "(`Word.isLt` supplies `len < 2^64`). With short+long1..long7 this "
        ++ "tiles every `len : Word`. ⚠️ INPUT-DOMAIN gate ONLY (`h_len_lo`); "
        ++ "`h_out_align`, `h_out_len` (`8 < |out|`), `h_out_valid` are ABI. "
        ++ "coverRef `len = 72057594037927936` — the long7/long8 boundary")
      (notes := "per-form (\"long8\") pinned triple; writes "
        ++ "`[0xFF, len >>> 56, …, len >>> 8, len]` and sets the cell flag to 9. "
        ++ "Step bound 90. ⭐ Loop CITED at `m := 8`. Canonical form via "
        ++ "`long8_first_length_byte_ne_zero`. Room `outPtr+9 ≤ 2^64` from "
        ++ "`h_out_valid`, not alignment"),

  -- #11291: the whole-routine triple already existed (landed 2026-07-17,
  -- closed #10782) but was never registered. It is `wdPrologue ;; wdBBField0`
  -- — the full program — not a per-path certificate, so a single row is the
  -- strongest claim and subsumes the Close2..5 composition chain.
  routine "withdrawal_decode" .proven (some "withdrawal_decode_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.withdrawal_decode`: decodes "
        ++ "all four RLP fields and returns `a0 = 0` with a `Decoded` verdict or "
        ++ "`a0 = 1` with a witnessed `DecodeFailure` — both paths in one triple, "
        ++ "so `.proven` and total (no input-domain gate). The intermediate WP "
        ++ "certificates in `WithdrawalDecode*WP.lean` are the steps this composes"),
  -- #11352 + #11578: `bgv_u32le`. Witness is offset form (covers unaligned a0).
  -- h_align listBase%8=0 is a CALLER assumption (ABI region base), NOT a static
  -- GuestAddrs pin discharged by decide — so `.conditional`, not `.proven`.
  -- coverRef `bgv_u32le_offset_precondition_reachable`. Flat form had the same
  -- gate as Region.wf on a0; moving it to listBase fixed production offs 4/12
  -- but did not erase the alignment hyp.
  routine "bgv_u32le" .conditional (some "bgv_u32le_offset_spec_within")
      (notes := "offset-form triple at GuestAddrs.bgv_u32le: a0=listBase+off "
        ++ "(may be unaligned), bytesRegion listBase bs, post a0=leU32 (bs.drop off) 0. "
        ++ "Gate: h_align listBase.toNat%8=0 remains a caller hyp at erh sites "
        ++ "(listBase is ABI a0, not a static GuestAddrs base). coverRef "
        ++ "`bgv_u32le_offset_precondition_reachable`. Prior flat_spec Region.wf "
        ++ "a0%8=0 does not cover offs 4/12. leU32_eq_bytesLEtoNat still ties value"),

  -- #11349: `check_gas_limit`, row 7 of docs/leaf-routine-targets.md. The machine
  -- triple already existed byte-transparently at the guest address; what this row
  -- registers is the model-facing restatement.
  routine "check_gas_limit" .proven (some "checkGasLimit_ref_spec")
      (notes := "whole-routine triple at `GuestAddrs.check_gas_limit`, post additionally "
        ++ "records `a0 = 0` iff `SpecRef.check_gas_limit` accepts. Full domain, NO "
        ++ "envelope hypothesis: the guest never forms the reference's two sums, it "
        ++ "compares |new - parent| against parent/1024"),

  -- #11344: `bytes_to_nibbles`, row 1 of docs/leaf-routine-targets.md. 10 fixture
  -- in-edges. Flat triple DERIVED from the SAsm `bytesToNibblesFn_spec` by
  -- `Fn.retSpecFlat`, so the counted loop's invariant stays in the SAsm proof.
  routine "bytes_to_nibbles" .proven (some "bytesToNibblesFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bytes_to_nibbles`: the destination "
        ++ "region holds `SpecRef.keyToNibbles (srcBytes.take len)` — the REFERENCE "
        ++ "function, not the routine's own accumulator. ABI hyps only (region wf, "
        ++ "non-overlap, non-overflow, aligned ra)"),

  -- #11799 dep / leaf-routine-targets row 4: whole-routine machine triple for
  -- `mpt_node_kind`. Full guest domain (arity-17 branch / arity-2 HP path /
  -- fail joins) with operational `MptNodeKindResult` post — no input-domain
  -- gate, so `.proven`. Pure `mptNodeKindSpec` (MptAssertions) is looser/stale
  -- vs the arity-exact guest; do not rest the post on it.
  -- #12027: Result→kindTag wiring under WF (success arms kind < 3) lands in
  -- MptNodeKindWire; existence + uniqueness witnessed below.
  routine "mpt_node_kind" .proven (some "mpt_node_kind_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.mpt_node_kind` / `kindB`: "
        ++ "count via `rlp_list_count_items`, nth via `rlp_list_nth_item` index 0, "
        ++ "HP nibble classify for leaf/ext. Post is operational "
        ++ "`MptNodeKindResult` (countFail/branch/badArity/nthFail/emptyPath/path). "
        ++ "POST STRENGTHEN (path preserve, free): x18..x21 stay concrete at "
        ++ "entry values — guest restores them via count/nth saves; old regOwn "
        ++ "export discarded that and blocked hop consumers. PRE unchanged "
        ++ "(already concrete v18..v21 in kindCallerPre/countAmbient). "
        ++ "#12027 wire: `mptNodeKindResult_eq_kindTag` (kind < 3) + "
        ++ "`mptNodeKindResult_exists_kindTag` under WF; encode-domain count "
        ++ "Success + path head HP; no #11341 (WF top-level .bytes only); "
        ++ "supersedes (does not consume) deleted pure guest_eq_kindTag bridge. "
        ++ "coverRef `mpt_node_kind_precondition_reachable`. Callees already "
        ++ "`.proven`; first walker-dispatch machine triple"),

  -- #11799: `hp_decode_nibbles` machine was already proved (HpDecodeNibblesSAsmPaths)
  -- but never registered — residual audit found it RETIRED as a walk dependency.
  -- callWithin adapter: HpDecodeNibblesCallSAsm.
  routine "hp_decode_nibbles" .proven (some "hp_decode_nibbles_spec_ported")
      (notes := "whole-routine triple at `GuestAddrs.hp_decode_nibbles` / symbolic "
        ++ "base: abiFrame over hdnBody; post is guest-exact `hdnRes` (= `hpDecode`) "
        ++ "into nibble buf + count/is-leaf cells. FULL DOMAIN (ABI hyps only). "
        ++ "Registered under #11799 residual audit — machine predated registration. "
        ++ "callWithin adapter `hp_decode_nibbles_call_spec_within` for walk ext/leaf"),

  -- #11574: the two field-bound scans. ⚠️ BOTH machine triples predate this
  -- registration by months and were simply never registered — a name search for
  -- the routines found nothing because the specs are in sibling `*SAsm` modules,
  -- which is the #10779 lesson recurring. What #11574 asked for that genuinely
  -- did not exist is the SpecRef vocabulary, not the triples.
  routine "u256_sub_be" .proven (some "u256SubBeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.u256_sub_be`: `[a2]` becomes "
        ++ "`u256SubBeBytes aBytes bBytes orig` (the 32-byte BE borrow chain) and "
        ++ "BOTH operand regions are pinned intact. ⚠️ Lives in "
        ++ "`Secp256k1FieldReduceOnceSAsmSupport.lean`, not a `U256*` module, and "
        ++ "its `CodeReq` is the shared `secfReduceOnceCr` rather than a "
        ++ "`CodeReq.ofProg` of its own — the flat triple was produced as support "
        ++ "for `secf_reduce_once`. ⚠️ A SECOND theorem of the same name exists in "
        ++ "`…ReduceOnceNSAsmSupport.lean` and is `private`; this row cites the "
        ++ "public one. Domain: 32-byte operands, disjoint from the output"),
  routine "u256_lt_be" .proven (some "u256LtBe_spec")
      (notes := "whole-routine triple at `GuestAddrs.u256_lt_be` over "
        ++ "`CodeReq.ofProg … u256LtBe_prog`, 295 steps: the output dword `[a2]` "
        ++ "is `1` iff `beBytesToNat as < beBytesToNat bs`, else `0`; `a0 = 0`; "
        ++ "BOTH 32-byte inputs pinned INTACT in the post, so a routine that "
        ++ "scribbled on its operands could not satisfy it. ABI hyps only "
        ++ "(lengths, 8-alignment, non-overflow, byte-access validity, aligned "
        ++ "ra) — no input-domain condition, so this is total over 32-byte "
        ++ "operands. ⭐ Highest-in-degree member of the u256 BE family (#12225); "
        ++ "the money path's comparison leg"),
  -- #12244: the two u256 BE members whose allowlist entries read "needs
  -- Fn.retSpecFlat before a .proven row is honest (#11637)". That debt is now
  -- paid, but by two DIFFERENT routes, which is the finding worth recording:
  --   * `u256_add_be` genuinely needed the lift (`Fn.retSpecFlatAmbient`).
  --   * `u256_is_zero` needed NO lift — a flat triple had been sitting in
  --     `Codegen/Proofs/U256IsZeroSpec.lean` since the port-playbook acceptance
  --     test, with only its `base` left free. The #12226 `--shape` classifier
  --     graded it "model-only" because it resolved the symbol to the SAsm
  --     structured spec `u256IsZeroFn_spec` and never saw the deployed one —
  --     the same one-theorem-per-symbol blind spot as the #12231 retraction,
  --     in the opposite direction. Both `(GuestAddrs.<sym>, <sym>_prog)` pairs
  --     were checked present in `GuestImageEntries`.
  routine "u256_add_be" .proven (some "u256AddBeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.u256_add_be` over "
        ++ "`CodeReq.ofProg … u256AddBe_prog`: the output window `[a2]` becomes "
        ++ "`u256AddBeBytes aBytes bBytes orig` (the 32-byte BE carry chain) and "
        ++ "`a0` is the CARRY-OUT — i.e. the 256-bit overflow flag, which the "
        ++ "contract publishes rather than discarding. `a1`/`a2` are republished "
        ++ "as the untouched operand/output pointers and BOTH 32-byte inputs are "
        ++ "pinned INTACT in the post. ABI hyps only (lengths 32, region wf, no "
        ++ "address wraparound, each operand range disjoint from the output "
        ++ "range, aligned ra). ⚠️ Deliberately does NOT mirror its "
        ++ "`u256_sub_be` sibling in two ways: the CodeReq is its own "
        ++ "`CodeReq.ofProg` rather than a caller's stage union "
        ++ "(`secfReduceOnceCr`), and the result register is exposed rather than "
        ++ "collapsed into `regOwns exposedRegs`. Lives in "
        ++ "`Codegen/Proofs/U256BeFlatTriples.lean`"),
  -- #12628: consumed by the header-validate path (`header_base_fee` K73/K74
  -- jal) but previously unrowed, so `check-axioms.sh` never audited it.
  routine "u256_eq" .proven (some "u256Eq_spec")
      (notes := "whole-routine triple over `u256EqBody` (byte-identical to "
        ++ "`u256Eq_prog` under any layout, `u256EqBody_flatten`): a0 = 1 "
        ++ "iff all 32 bytes match (firstDiff bs1 bs2 32 = 32), else 0. "
        ++ "Static preconditions only — 32-byte operand widths, pointer "
        ++ "bounds, and bnfEq32-style window disjointness — which is the ABI, "
        ++ "not a domain gate."),
  routine "u256_is_zero" .proven (some "u256IsZeroFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.u256_is_zero` over "
        ++ "`CodeReq.ofProg … u256IsZero_prog`, 9 steps: loads the four dwords "
        ++ "at `ptr/+8/+16/+24`, ORs them, and returns `a0 = 1` iff the OR is "
        ++ "zero. Memory is UNTOUCHED (the four dword atoms are pinned in the "
        ++ "post). ABI hyps only (aligned ra) — no input-domain condition, so "
        ++ "it is total. Data-independent timing: no short-circuit. A companion "
        ++ "`u256IsZeroFlat_spec_domain` restates the result as "
        ++ "`if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0`, which is the form a "
        ++ "caller's `callWithin` residual wants. ⚠️ This row cites the ANCHORED "
        ++ "instantiation; the free-`base` original is "
        ++ "`u256_is_zero_deployed_spec` in the same module"),
  -- #12244 third member. This one required a change to the LEAF's contract
  -- before any adapter could reach it: `u256FromU64BeFn`'s post was
  -- ambient-AGNOSTIC (`fun _ ws _ => ws = u256FromU64Bytes v`), so neither
  -- `Fn.retSpecFlat`'s `hpostEmp` nor `Fn.retSpecFlatAmbient`'s `hpostAmb` was
  -- dischargeable — both need the post to PIN the ambient, that being the only
  -- way the fact survives out of the existential `asrtOf`. The ambient is now
  -- pinned to `empAssertion` in the leaf's pre AND post, which is the honest
  -- ambient for a routine with no read-only input region.
  routine "u256_from_u64_be" .proven (some "u256FromU64BeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.u256_from_u64_be` over "
        ++ "`CodeReq.ofProg … u256FromU64Be_prog`, 19 steps: zero-extends the "
        ++ "64-bit value in `a0` into the 32-byte BE window at `a1`, which "
        ++ "becomes `u256FromU64Bytes v`. ABI hyps only (output region wf, 32 "
        ++ "original bytes, aligned ra) — no input-domain condition, so it is "
        ++ "TOTAL over the 64-bit input. Lives in "
        ++ "`Codegen/Proofs/U256BeFlatTriples.lean`"),
  -- K54 whole-routine entry triple. The K70/K73 callers are the dated next
  -- consumers; this row makes the theorem visible to the registry and axiom
  -- gate before those adapters consume it.
  routine "u256_mul_u64_be" .proven (some "mulWhole_spec")
      (notes := "whole-routine triple at `GuestAddrs.u256_mul_u64_be` over "
        ++ "`mulCR`, 3850 steps: zero-fills the accumulator, multiplies the "
        ++ "32-byte big-endian source by the u64 operand, copies the result, "
        ++ "and preserves the caller-owned input/output regions. ABI/resource "
        ++ "hypotheses only, so no input-domain gate. The dated consumers are "
        ++ "K70 `header_validate_excess_blob_gas + 104` and K73 "
        ++ "`eip1559_calc_base_fee_per_gas + 84` (2026-08-16); their adapters "
        ++ "are the next wiring step, not silently claimed here."),
  -- #12461 arm 2. Amsterdam passes the source and output pointers equal;
  -- this is a separate contract, not a weakening of the disjoint one above.
  routine "u256_mul_u64_be" .proven (some "mulWhole_inPlace_spec")
      (notes := "separate single-pointer alias contract at "
        ++ "`GuestAddrs.u256_mul_u64_be`, 3850 steps: the outer loop reads "
        ++ "the 32-byte source before the reverse copy writes the result in "
        ++ "the same window. The caller-owned source/output region is therefore "
        ++ "safe for Amsterdam arm 2; ordinary partial overlap remains outside "
        ++ "the contract. The dated Amsterdam witness discharges "
        ++ "C = 11,684,671 at both division sites."),
  -- Shared callee of both K70 and K74. The existing flat theorem is already
  -- anchored to this routine's own CodeReq, so this row exposes it directly.
  routine "u256_div_u64_be" .conditional (some "u256DivU64BeInPlaceFlat_spec")
      (gate := "nonzero divisor `0 < b < 2^64`; the remaining hypotheses "
        ++ "are ABI/resource facts")
      (notes := "whole-routine triple at `GuestAddrs.u256_div_u64_be` over "
        ++ "`CodeReq.ofProg … u256DivU64Be_prog`: processes a 32-byte "
        ++ "big-endian source into the 32-byte quotient window and returns "
        ++ "the final remainder in `a0`, preserving the divisor, output "
        ++ "pointer, source region and scratch ownership. The source/output "
        ++ "`u256DivU64BeInPlaceFlat_spec` is the consumed exact-alias contract "
        ++ "for K73's calls; partial overlap is not safe. Together with the "
        ++ "original disjoint-source/output contract, the safe premise is "
        ++ "`srcPtr = outPtr` or `srcPtr + 32 ≤ outPtr` or "
        ++ "`outPtr + 32 ≤ srcPtr`. `0 < b < 2^64` is the "
        ++ "genuine input-domain restriction; the Word representation supplies "
        ++ "the upper bound. This is the shared arithmetic callee "
        ++ "for K70 and K74; K70's +168 call supplies the checked product "
        ++ "`0xb24b3f * x18` (with `x18` initialized to 1), K70's +192 "
        ++ "call supplies literal `0xb24b3f`, and K73's +120/+168 calls "
        ++ "supply literal `8`. K73's +104 call supplies `gas_limit >> 1`, "
        ++ "discharged by its `gas_limit ≥ 2` caller precondition; K74 reaches "
        ++ "these through K73. Lives in "
        ++ "`Codegen/Programs/U256DivU64BeSAsm.lean`"),
  -- #12461 arm 4: a concrete full-premise inhabitant of the K73 increasing
  -- entry/status-zero composition.  This is deliberately `.partly`: the
  -- theorem is a real status-zero arm composition with its all-outcome post,
  -- but it is not yet the unconstrained whole-routine K73 contract.
  routine "eip1559_calc_base_fee_per_gas" .partly
      (some "k73_increase_entry_status_div_zero_live_spec_within")
      (notes := "live full-premise inhabitants of the K73 increasing arm: base "
        ++ "fee bytes encode 7 or 1,000,000, gas_limit = gas_used = 5,000, "
        ++ "and target = 2,500. The base-fee-7 witness covers the "
        ++ "max-with-one clamp arm with q1 = 7 and q2 = 0; the "
        ++ "base-fee-1,000,000 witness covers the nonzero first divide/add "
        ++ "route with q1 = 1,000,000 and q2 = 125,000. The proofs compose "
        ++ "the existing `mulWhole_spec` callee adapter and name five consumed "
        ++ "composition witnesses: "
        ++ "`k73_increase_entry_to_mul_spec_within`, "
        ++ "`k73_increase_status_div_zero_spec_within_for_return`, "
        ++ "`k73_increase_first_div_source_branch_for_return`, "
        ++ "`k73_increase_second_add_branch_for_return`, and "
        ++ "`k73_increase_second_div_source_branch_for_return`. The two live "
        ++ "inhabitants cover those distinct arms; these are concrete-first "
        ++ "non-vacuity witnesses for the status-zero route, not "
        ++ "a claim that every K73 input is covered; the generic unconstrained "
        ++ "entry theorem remains open. No emitted code changes."),
  -- #12244 ask 3, first harvest from the MECHANICAL queue that
  -- `scripts/ambient-triage.py` computes. That triage partitions the `--shape`
  -- model-only bucket by whether the leaf `Fn`'s post PINS its ambient — the
  -- property every adapter in `Rv64/SAsm/FnFlat.lean` requires — into
  -- mechanically-liftable, needs-a-leaf-contract-change-first, and NOT ANCHORED
  -- (no GuestAddrs + GuestImageEntries pair, hence liftable but never rowable).
  -- That third class is why "lift in in-degree order", as the issue originally
  -- proposed, was the wrong queue: in-degree is the value, the triage is the cost
  -- and whether a row is possible at all.
  -- ⚠️ Deliberately no bucket counts here: they move every time a row lands, and
  -- a literal in prose is the drift class #12129/#12103 keep re-finding. Run
  -- `python3 scripts/ambient-triage.py` for the live split, and
  -- `--self-test` to confirm the classifier still reproduces the hand-established
  -- verdicts from #12283.
  -- This row is the validation that the mechanical queue is real: the proof is the
  -- `u256AddBeFlat_spec` template with the operand shapes swapped, no new insight.
  routine "bnf_eq32" .proven (some "bnfEq32Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnf_eq32` over "
        ++ "`CodeReq.ofProg … bnfEq32_prog`: `a0` becomes `1` iff the two "
        ++ "32-byte BN254 field elements at `a0`/`a1` are byte-equal, else `0` "
        ++ "(stated as `firstDiff bs1 bs2 32 = 32`). BOTH operand regions are "
        ++ "pinned INTACT in the post, so a routine that scribbled on its inputs "
        ++ "could not satisfy it. ABI hyps only (both regions wf, both lengths "
        ++ "32, no address wraparound, ranges disjoint, aligned ra) — no "
        ++ "input-domain condition, so total over 32-byte operands. Geometry is "
        ++ "the MIRROR of `u256_add_be`: non-empty read-only `region` riding "
        ++ "through as the trailing conjunct, EMPTY writable `rw`. Lives in "
        ++ "`Codegen/Proofs/AmbientLiftedFlatTriples.lean`"),
  -- The remaining three members of the `(a0, a1) -> a0` compare family. All four
  -- now share ONE proof: `eqFamilyFlatSpec` in the same module, of which these
  -- and `bnf_eq32` are instantiations. Each discharges a
  -- `registry-coverage-allow.txt` entry whose stated reason was exactly "needs
  -- Fn.retSpecFlat before a .proven row is honest" (#11637) — so the exemption is
  -- DISCHARGED, not moved.
  routine "secf_eq32" .proven (some "secfEq32Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.secf_eq32` over "
        ++ "`CodeReq.ofProg … secfEq32_prog`: `a0` becomes `1` iff the two "
        ++ "32-byte secp256k1 field elements at `a0`/`a1` are byte-equal, else "
        ++ "`0` (stated as `Secp256k1FieldEq32SAsm.firstDiff bs1 bs2 32 = 32`). "
        ++ "BOTH operand regions pinned INTACT in the post. ABI hyps only — no "
        ++ "input-domain condition, so total over 32-byte operands. An "
        ++ "instantiation of `eqFamilyFlatSpec`, not a separate proof. Lives in "
        ++ "`Codegen/Proofs/AmbientLiftedFlatTriples.lean`"),
  routine "p256_eq32" .proven (some "p256Eq32Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.p256_eq32` over "
        ++ "`CodeReq.ofProg … p256Eq32_prog`. The body is LITERALLY "
        ++ "`secfEq32Body` (`P256Eq32SAsm.lean:20`), not merely similar, which "
        ++ "is why the post is stated with "
        ++ "`Secp256k1FieldEq32SAsm.firstDiff` rather than a `p256`-named copy. "
        ++ "BOTH operand regions pinned INTACT; ABI hyps only, total over "
        ++ "32-byte operands. An instantiation of `eqFamilyFlatSpec`. Lives in "
        ++ "`Codegen/Proofs/AmbientLiftedFlatTriples.lean`"),
  routine "blsg_eq48" .proven (some "blsgEq48Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg_eq48` over "
        ++ "`CodeReq.ofProg … blsgEq48_prog`: the 48-byte member of the compare "
        ++ "family (BLS12-381 G1 field elements), `a0` becomes `1` iff "
        ++ "byte-equal (`Bls12G1Eq48SAsm.firstDiff bs1 bs2 48 = 48`). BOTH "
        ++ "operand regions pinned INTACT; ABI hyps only, total over 48-byte "
        ++ "operands. Instantiates `eqFamilyFlatSpec` IDENTICALLY to the 32-byte "
        ++ "cases — the width lives entirely in `fn.pre`/`fn.post`, so the "
        ++ "family lemma needs no width parameter. Non-vacuity is witnessed by "
        ++ "`blsgEq48Flat_instance`, stated with no numeric guest address. Lives "
        ++ "in `Codegen/Proofs/AmbientLiftedFlatTriples.lean`"),
  -- FOURTH geometry in the ambient-lift harvest: empty read-only `region`,
  -- non-empty writable `rw`, EMPTY ambient, and four ABI argument registers. So
  -- it takes the ambient-FREE `Fn.retSpecFlat`, mirroring `u256_from_u64_be`
  -- rather than the compare family. Discharges another #11637 allowlist entry.
  routine "call_frame_set_calldata" .proven (some "callFrameSetCalldataFlat_spec")
      (notes := "whole-routine triple at "
        ++ "`GuestAddrs.call_frame_set_calldata` over `CodeReq.ofProg … "
        ++ "callFrameSetCalldata_prog`: writes the calldata pointer "
        ++ "`parentMem + argsOff` at offset 416 and the length `argsLen` at 424 "
        ++ "of the 432-byte child call frame based at `a0`. The rest of the frame "
        ++ "is BYTE-FOR-BYTE preserved — the post is a `setBytes … setBytes` of "
        ++ "the ORIGINAL contents, not a havoc, so a routine that clobbered any "
        ++ "other frame byte could not satisfy it. All FOUR argument registers "
        ++ "`a0`–`a3` are pinned in the post (the leaf's post supplies them, and "
        ++ "a caller sequencing several `call_frame_*` writes needs the frame "
        ++ "pointer still in `a0`); that is a proved property of these three "
        ++ "instructions, NOT a callee-saved ABI guarantee other routines share. "
        ++ "Domain: `RwRegion.wf ⟨childEnv, 432⟩`, a 432-byte original frame, "
        ++ "aligned `ra` — no input-domain condition, so total over well-formed "
        ++ "frames. Lives in "
        ++ "`Codegen/Proofs/CallFrameCalldataFlatTriple.lean`"),
  -- FIFTH geometry: non-empty read-only `region`, EMPTY writable `rw`, EMPTY
  -- ambient — the read-only accessor shape. Takes the ambient-free
  -- `Fn.retSpecFlat`, and needed no leaf contract change because its post
  -- already pins `A = empAssertion`.
  routine "secf_get_bit_lsb" .proven (some "secfGetBitLsbFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.secf_get_bit_lsb` over "
        ++ "`CodeReq.ofProg … secfGetBitLsb_prog`: `a0` becomes the LSB-indexed "
        ++ "bit `a1` of the 32-byte secp256k1 field element at `a0` "
        ++ "(`secfGetBitLsbResult`). The operand region is pinned INTACT and "
        ++ "there is NO writable window at all, so the routine provably touches "
        ++ "no memory — one that scribbled anywhere could not satisfy it. "
        ++ "⚠️ NOT total over its argument type, unlike the compare family: the "
        ++ "domain carries a genuine input condition, `Region.loadOk` for the "
        ++ "byte the index selects, which is what puts the bit index in range. "
        ++ "Fifth `Fn` geometry in the harvest (non-empty region, EMPTY rw, "
        ++ "EMPTY ambient) so it takes the ambient-free `Fn.retSpecFlat`. "
        ++ "⚠️ The theorem lives in `Codegen/Programs/Secp256k1FieldGetBitLsbSAsm.lean` "
        ++ "(landed de2fc7fe0), NOT in the ambient-free proofs module: a duplicate "
        ++ "was written there and removed. Its non-vacuity — including the "
        ++ "negative control showing `hload` is FALSE at `bitIdx = 256`, so the "
        ++ "bundle can be contradicted — is in "
        ++ "`Codegen/Proofs/AmbientFreeFlatTriples.lean`"),
  -- Same fifth geometry, one argument. ⚠️ Its three nearest siblings
  -- (`enrg_u32le`, `spw_u32le`, `sws_u32le`) are the SAME computation but their
  -- posts discard the ambient binder, so they are NOT liftable — family
  -- resemblance in the name does not predict liftability, only the `post` does.
  routine "bah_u32le" .proven (some "bahU32leFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bah_u32le` over "
        ++ "`CodeReq.ofProg … bahU32le_prog`: `a0` becomes the little-endian "
        ++ "`u32` at `a0` (`SgLoadU32leSAsm.leU32 bs 0`). As with "
        ++ "`secf_get_bit_lsb`, `rw` is EMPTY and the operand region is pinned "
        ++ "INTACT, so the routine provably touches no memory. Domain: ABI plus "
        ++ "`4 ≤ bs.length` — a genuine condition, but on the BUFFER rather than "
        ++ "a numeric argument, so every caller passing a wide enough region "
        ++ "satisfies it. ⚠️ This leaf's post is `fun rf _ A => …` and does NOT "
        ++ "pin `ws`, so emptiness of the written window comes from the length "
        ++ "side condition (`rw` empty ⇒ `ws.length = 0`) rather than the post. "
        ++ "⚠️ The theorem lives in `Codegen/Programs/BlockAccessListHashSAsm.lean` "
        ++ "(landed a9c898904, first member of the #12328 contract-first "
        ++ "burn-down), NOT in the ambient-free proofs module: a duplicate was "
        ++ "written there and removed. The stale allowlist entry claiming this "
        ++ "symbol still needed `Fn.retSpecFlat` is what hid it. Its non-vacuity "
        ++ "is in `Codegen/Proofs/AmbientFreeFlatTriples.lean`"),
  -- Second of the four allowlist entries whose ONLY obstacle was a union CodeReq.
  routine "secf_is_zero32" .proven (some "secfIsZero32FlatEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.secf_is_zero32` over "
        ++ "`CodeReq.ofProg … secfIsZero32_prog`: `a0` becomes 1 iff the 32-byte "
        ++ "buffer at `a0` is all-zero (`WhileBreakDemo.nlz bs 32 = 32`). `rw` is "
        ++ "EMPTY and the operand region is pinned INTACT, so the routine provably "
        ++ "touches no memory. Domain: ABI plus `bs.length = 32` and a no-wrap "
        ++ "bound — both conditions on the BUFFER, not on a numeric argument. "
        ++ "⚠️ Same CodeReq trap as `secf_zero32`: the pre-existing "
        ++ "`Secp256k1PointDoubleSAsmStage.secfIsZero32Flat_spec` is anchored over "
        ++ "`pdCr`, a union requiring FIVE programs loaded, so it is NOT the image "
        ++ "claim and was not rowable. This row cites the own-CodeReq sibling. "
        ++ "Lives in `Codegen/Proofs/AmbientFreeFlatTriples.lean`"),
  -- Geometry of `u256_from_u64_be` (empty region, non-empty rw, EMPTY ambient)
  -- with one argument, so it reuses that split rather than adding its own.
  routine "secf_zero32" .proven (some "secfZero32FlatEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.secf_zero32` over "
        ++ "`CodeReq.ofProg … secfZero32_prog`: the 32-byte window at `a0` "
        ++ "becomes `List.replicate 32 0` — the WHOLE window, so a routine that "
        ++ "zeroed only a prefix could not satisfy it. Domain: ABI only, so this "
        ++ "one IS total over its argument type. ⚠️ Distinct from the "
        ++ "near-identical `Secp256k1PointDoubleSAsmStage.secfZero32Flat_spec`, "
        ++ "which is anchored over `pdCr` — a four-fold `.union` requiring FIVE "
        ++ "programs to be loaded. This row cites the version whose `CodeReq` is "
        ++ "the routine's own program, matching the `GuestImageEntries` pairing; "
        ++ "hence the `…FlatEntry_spec` name. ⛔ CORRECTION (#12244): this note "
        ++ "used to say the twin needs the five `pdCr` ranges pairwise disjoint "
        ++ "and was NOT proved. The first half is wrong — `liftCode … (by "
        ++ "code_mem)` discharges own-`CodeReq` ⊆ `pdCr` directly, as the two "
        ++ "converter contracts in `Secp256k1PointDoubleSAsmStage` now demonstrate "
        ++ "against `pdCr` itself. What actually blocks collapsing THIS twin is "
        ++ "only statement alignment: the `pdCr` copy quantifies "
        ++ "`(secfZero32Fn 0 []).body.steps` where this triple uses "
        ++ "`(secfZero32Fn dst orig).body.steps`, and names the same register list "
        ++ "`a0Rest` rather than `resScratch`. Tracked as a follow-up. Lives in "
        ++ "`Codegen/Proofs/AmbientFreeFlatTriples.lean`"),
  -- The last entry of the "false tier A, RETRACTED 2026-08-12" block in
  -- `scripts/registry-coverage-allow.txt` — and it needed NO proof work at all.
  -- ⭐ That entry sent the reader to the CALLER's stage file
  -- (`Bls12G2EncodeSAsm`, `encCr`) as if the caller union were the only flat
  -- triple. It was wrong: an own-`CodeReq` triple has been sitting in the
  -- routine's OWN module the whole time, referenced by nothing. Its `hsize`
  -- hypothesis is why the suffix heuristic and the per-symbol read both slid
  -- past it. Grep the symbol WITHOUT `| head` — truncation is how I missed it
  -- on the first pass here.
  routine "blsg_le_to_be" .proven (some "blsgLeToBeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg_le_to_be` over "
        ++ "`blsgLeToBeCr = CodeReq.ofProg (GuestAddrs.blsg_le_to_be) "
        ++ "blsgLeToBe_prog` — the single-program `GuestImageEntries` pairing, so "
        ++ "this IS the image claim: the 48-byte LITTLE-ENDIAN buffer at `a0` "
        ++ "becomes its BIG-ENDIAN encoding `blsgLeToBeBytes inb` at `a1`, with "
        ++ "the source region pinned INTACT and `ra` preserved. The post is "
        ++ "DETERMINISTIC (a named byte function, not an existential), which is "
        ++ "stronger than the ∃-post the secp256k1 converters carry. Domain: ABI "
        ++ "plus `frameOk src dst` — unfolding to `src+48 < 2^64 ∧ dst+48 < 2^64 ∧ "
        ++ "(src+48 ≤ dst ∨ dst+48 ≤ src)`, the same window-disjointness that any "
        ++ "both-regions-live geometry forces, satisfiable at e.g. `src = 0`, "
        ++ "`dst = 48` — plus an explicit `hsize` step-count bound discharged by "
        ++ "`decide` at each call site. ⚠️ NAME COLLISION, three ways: "
        ++ "`Bls12G2EncodeSAsm.blsgLeToBeFlat_spec` (over `encCr`) and "
        ++ "`Bls12KzgG2WireSAsm.blsgLeToBeWireFlat_spec` (over `wireCr`) are "
        ++ "caller unions, NOT the image claim; both are now one-line corollaries "
        ++ "of this row's theorem. This row cites the one in "
        ++ "`Codegen/Programs/Bls12G1LeToBeSAsm.lean`"),
  -- ⭐ Rowed the same hour #12380 landed the triple. That PR added an own-`CodeReq`
  -- flat triple for this symbol and did NOT row it, leaving the allowlist saying
  -- tier B / "needs `Fn.retSpecFlat` before a `.proven` row is honest" — false the
  -- moment it merged. Every PR that lands a flat triple should either row it or say
  -- why not; #11637 exists because the gap is invisible otherwise.
  routine "blsg_be_to_le" .proven (some "blsgBeToLeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg_be_to_le` over "
        ++ "`blsgBeToLeCr = CodeReq.ofProg (GuestAddrs.blsg_be_to_le) "
        ++ "blsgBeToLe_prog`, exactly the `GuestImageEntries` pairing, so it is the "
        ++ "image claim: the 48-byte BIG-ENDIAN buffer at `a0` becomes six "
        ++ "LITTLE-ENDIAN u64 limbs at `a1`. The post is `blsgBeToLeOutput dst "
        ++ "inBytes` — existential in the written bytes, pinning the 384-bit decode "
        ++ "`Accel.leLimbsToNat [wsDword out 0, …, wsDword out 40] = beBytesToNat "
        ++ "inBytes` — with the source region pinned INTACT. Same "
        ++ "both-regions-non-empty geometry as the `secf` converters, so it carries "
        ++ "the same window-disjointness `hdisj` and is NOT total over its argument "
        ++ "types, plus a `decide`-able `hsz` step bound. ⚠️ Unlike its "
        ++ "`blsg_le_to_be` twin there is only ONE theorem of this name, and the "
        ++ "callers consume it directly rather than through a union sibling"),
  -- ⭐ THE SAME CLASS AGAIN, found by generalising the `blsg_le_to_be` lesson to the
  -- rest of the tier-A allowlist: check the routine's OWN module before believing an
  -- entry that names a caller's file. `blq_zero`'s entry named
  -- `Bls12Fq12SetOneSAsm.lean`, whose `blqCr` requires the CONCATENATION
  -- `blqZero_prog ++ blqSetOne_prog` at this address — an adjacency assumption about
  -- two routines, not the single-program image pairing. The own-`CodeReq` triple was
  -- in `Bls12Fq12ZeroSAsm.lean` all along.
  routine "blq_zero" .proven (some "blqZeroFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blq_zero` over "
        ++ "`blqZeroCr = CodeReq.ofProg (GuestAddrs.blq_zero) blqZero_prog` — "
        ++ "byte-for-byte the `GuestImageEntries` pairing `(GuestAddrs.blq_zero, "
        ++ "blqZero_prog)`, so this IS the image claim: the 576-byte window at `a0` "
        ++ "becomes `List.replicate 576 0` — the WHOLE window, deterministic, not an "
        ++ "existential and not a prefix. Domain: ABI only (`RwRegion.wf ⟨dst, 576⟩`, "
        ++ "`orig.length = 576`, a `decide`-able step-count bound, aligned `ra`), so "
        ++ "this one IS total over its argument type — no disjointness side condition, "
        ++ "because `rw` is the only live window. ⚠️ NAME COLLISION: "
        ++ "`Bls12Fq12SetOneSAsm.blqZeroFlat_spec` has the SAME name and a different "
        ++ "statement (it takes `vs : List Word`) anchored over `blqCr`, which demands "
        ++ "`blqZero_prog ++ blqSetOne_prog` at this address — an adjacency claim about "
        ++ "TWO routines and therefore stronger than the image pairing. That one is "
        ++ "not rowable as this symbol's claim. This row cites the one in "
        ++ "`Codegen/Programs/Bls12Fq12ZeroSAsm.lean`"),
  -- #12568: found by sweeping for triples the coverage census cannot see. This one was
  -- invisible for THREE independent reasons, none of them a missing proof:
  --   1. the theorem is `blqSetOneFrame_spec` — an EXTRA `Frame` component, so the
  --      name-based mapping strips `_spec` and lands on `blq_set_one_frame`, which is
  --      not a linked symbol (the #12568 namespace rule does not catch this variant:
  --      here the symbol is a PREFIX of the stripped name, not a suffix);
  --   2. its entry is spelled `(GuestAddrs.blq_zero + 24)`, not
  --      `GuestAddrs.blq_set_one` — equal by `decide` (0x800383c8 + 24 = 0x800383e0),
  --      but invisible to any check keyed on the symbol's own citation;
  --   3. `blqCr` names two programs, which the `blq_zero` row above correctly rejects
  --      for THAT symbol.
  -- ⭐ On (3) the caller/callee distinction is what makes this row honest, exactly as
  -- for `secp256k1_point_double`/`pdCr`: `blq_set_one` CALLS `blq_zero` (`jal ra,
  -- blq_zero` in its body), so `blqCr` is its caller∪callee code map, not an
  -- over-assumption. And it is derivable from the two `GuestImageEntries` pairings —
  -- `(blq_zero, blqZero_prog)` and `(blq_set_one, blqSetOne_prog)` — plus contiguity,
  -- which is `#guard`-checked in the module: `GuestAddrs.blq_zero + 4 *
  -- blqZero_prog.length = GuestAddrs.blq_set_one` with `blqZero_prog.length = 6`.
  -- For the CALLEE `blq_zero` the same CodeReq would over-assume; that row says so.
  routine "blq_set_one" .proven (some "blqSetOneFrame_spec")
      (notes := "whole-routine ABI contract for `blq_set_one` at its guest address, "
        ++ "spelled `(GuestAddrs.blq_zero + 24)` — equal to `GuestAddrs.blq_set_one` by "
        ++ "`decide` (0x800383c8 + 24 = 0x800383e0). Over `blqCr = CodeReq.ofProg "
        ++ "(GuestAddrs.blq_zero) (blqZero_prog ++ blqSetOne_prog)`: the CALLER∪CALLEE "
        ++ "map, since this routine's body is `mv s0,a0; jal ra, blq_zero; li; sd` — "
        ++ "the same posture as `secp256k1_point_double` over `pdCr`, and NOT the "
        ++ "over-assumption the `blq_zero` row above rejects for the callee. "
        ++ "Contiguity is `#guard`-checked (`blq_zero + 4 * blqZero_prog.length = "
        ++ "blq_set_one`, `blqZero_prog.length = 6`), so the concatenation is exactly "
        ++ "the two `GuestImageEntries` pairings side by side. Byte-transparency is "
        ++ "kernel-checked: `setOneProg_eq : abiFrameProg (-16) (16) setOneFrame "
        ++ "setOneBody = blqSetOne_prog := rfl`. POST is the genuine, unweakened "
        ++ "semantics: the FQ12 window at the entry `a0` holds ONE — dword 0 = 1 and "
        ++ "dwords 1–71 = 0, the WHOLE 72-dword window deterministically, not an "
        ++ "existential and not a prefix — `a0` ends at `dst + 576`, and `sp`/`ra`/`s0` "
        ++ "are restored to ENTRY values (`ra` was clobbered by the real cross-call, "
        ++ "`s0` by the body). The callee contract used is the adapter-derived "
        ++ "`blqZeroFlat_spec`, so the caller owns the callee's full exposed-register "
        ++ "footprint across the call (`regOwns blqRiders`). Domain: ABI only "
        ++ "(`vs.length = 72`, `RwRegion.wf ⟨dst, 576⟩`, aligned `ra`) — total over its "
        ++ "argument types, no disjointness side condition. ⚠️ NO NEW PROOF: the "
        ++ "theorem already existed; it was invisible to the coverage census (#12568). "
        ++ "Lives in `Codegen/Programs/Bls12Fq12SetOneSAsm.lean`"),
  -- The LAST TWO members of the union-`CodeReq` class (#12244). Unlike the four
  -- before them these needed no new proof at all: BOTH callers
  -- (`…FieldMulModPSAsmStage`, `…PointDoubleSAsmStage`) already contained a
  -- character-identical flat triple differing only in `mulCr` / `pdCr`, and each
  -- built the own-`CodeReq` triple internally via `Fn.retSpecFlat` before widening
  -- it with `liftCode`. Naming that intermediate step made all four copies
  -- one-line `⊆`-monotonicity corollaries and removed ~360 duplicated lines.
  routine "secf_be_to_le" .proven (some "secfBeToLeFlatEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.secf_be_to_le` over "
        ++ "`CodeReq.ofProg … secfBeToLe_prog`, the `GuestImageEntries` pairing: "
        ++ "the 32-byte BIG-ENDIAN buffer at `a0` becomes four LITTLE-ENDIAN u64 "
        ++ "limbs at `a1`. The post is existential in the written BYTES and pins "
        ++ "their decode — `wsNat256 ws' 0 = beBytesToNat inb` — which is the "
        ++ "converter's whole functional content; the source region is pinned "
        ++ "INTACT. First rowed member of the both-regions-non-empty geometry "
        ++ "(read-only `region` AND writable `rw` both live), which is exactly why "
        ++ "it carries a window-disjointness hypothesis `hdisj` that the "
        ++ "single-window leaves do not: a genuine domain restriction discharged "
        ++ "by the arena layout at each call site, NOT a representability guard, "
        ++ "so this triple is not total over its argument types. ⚠️ Distinct from "
        ++ "the two pre-existing `secfBeToLeFlat_spec`s in the caller stage files, "
        ++ "anchored over `mulCr` (3 programs) and `pdCr` (5 programs); those are "
        ++ "caller-specific assumptions, not the image claim. Both are now "
        ++ "corollaries of this row's theorem. Lives in "
        ++ "`Codegen/Programs/Secp256k1FieldConvFlatEntry.lean`"),
  routine "secf_le_to_be" .proven (some "secfLeToBeFlatEntry_spec")
      (notes := "the inverse converter, whole-routine triple at "
        ++ "`GuestAddrs.secf_le_to_be` over `CodeReq.ofProg … secfLeToBe_prog`: "
        ++ "four LITTLE-ENDIAN u64 limbs at `a0` become a 32-byte BIG-ENDIAN "
        ++ "buffer at `a1`, with the post pinning `beBytesToNat ws' = "
        ++ "wsNat256 inb 0` and the source region INTACT. Same "
        ++ "both-regions-non-empty geometry and same `hdisj` domain restriction as "
        ++ "its `secf_be_to_le` twin. ⚠️ The `pdCr` copy this replaces also carried "
        ++ "an `Accel.leLimbsToNat [wsDword inb 0, …] = wsNat256 inb 0` bridge; "
        ++ "that identity holds by `rfl`, so the rowed statement is the "
        ++ "`wsNat256` one and nothing was weakened to get it. Lives in "
        ++ "`Codegen/Programs/Secp256k1FieldConvFlatEntry.lean`"),
  -- #12244 ask 3, second harvest — and this one needed NO lift at all, which is
  -- the other thing `ambient-triage.py` reports. Its ⭐ heuristic (symbol anchor
  -- and a `cpsTripleWithin` in the same module) flagged `secf_copy32`, and the
  -- flag was right: `secfCopy32Direct_spec` has been a whole-routine flat triple
  -- at `GuestAddrs.secf_copy32` all along. So this symbol's allowlist entry —
  -- "needs Fn.retSpecFlat before a .proven row is honest" — was provably FALSE,
  -- the same stale-claim class as `u256_is_zero` in #12283. Check every ⭐ before
  -- writing a proof.
  routine "secf_copy32" .proven (some "secfCopy32Direct_spec")
      (notes := "whole-routine triple at `GuestAddrs.secf_copy32`, 9 steps: the "
        ++ "32 bytes at `a1` become the 32 bytes at `a0` (four dword copies), the "
        ++ "SOURCE region is pinned INTACT in the post, and `a0`/`a1` are "
        ++ "preserved while `t0` is owned. Full effect, not a weakened post. ABI "
        ++ "hyps only (both lengths 32, aligned ra). ⚠️ Its `CodeReq` is the "
        ++ "shared stage union `secfReduceOnceCr` rather than a `CodeReq.ofProg` "
        ++ "of its own — the same caveat as the `u256_sub_be` row — but that "
        ++ "union provably contains `CodeReq.ofProg (GuestAddrs.secf_copy32) "
        ++ "secfCopy32_prog`, so the anchor is the image's real code. ⚠️ A SECOND "
        ++ "theorem of the same name exists in `…ReduceOnceNSAsmSupport.lean` and "
        ++ "is `private`; this row cites the PUBLIC one in "
        ++ "`Secp256k1FieldReduceOnceSAsmSupport.lean`"),
  -- #12568: the 4th and 5th members of the `…Frame_spec` invisible class, and the
  -- pair that shows the mangling can be worse than a clean extra component:
  -- `secfReduceOnceNFrame` camel-snakes to `secf_reduce_once_nframe` — the `N` does
  -- not separate from `Frame` — so it misses `secf_reduce_once_n` by more than one
  -- token. Both are whole-routine triples at their own symbol over a FOUR-way
  -- caller∪callee union of `ofProg`s at REAL guest addresses (self ∪ `u256_lt_be` ∪
  -- `u256_sub_be` ∪ `secf_copy32`, all three callees rowed), with byte-transparency
  -- kernel-checked as `abiFrameProg … = …_prog := rfl`. NO NEW PROOF.
  routine "secf_reduce_once" .proven (some "secfReduceOnceFrame_spec")
      (notes := "whole-routine ABI contract at `GuestAddrs.secf_reduce_once` over "
        ++ "`secfReduceOnceCr` — the routine's own `CodeReq.ofProg … "
        ++ "secfReduceOnce_prog` unioned with `u256_lt_be`, `u256_sub_be` and "
        ++ "`secf_copy32`, every leg an `ofProg` at a REAL guest address, i.e. the "
        ++ "standard caller∪callee map (all three callees are themselves rowed). "
        ++ "Byte-transparency kernel-checked: `abiFrameProg … secfReduceOnceFrame "
        ++ "secfReduceOnceBody = secfReduceOnce_prog := rfl`. Conditional single "
        ++ "reduction mod p: if the 32-byte big-endian value at `src` is ≥ "
        ++ "`secp256k1_p_be` it is reduced by one subtraction into `dst`, else copied "
        ++ "unchanged — both arms inside the claim. `sp`/`ra`/`s0`/`s1` restored to "
        ++ "ENTRY values. ⚠️ NOT total: carries window-disjointness hypotheses against "
        ++ "`GuestAddrs.secp256k1_p_be` and `dst`, a genuine domain restriction "
        ++ "discharged by the arena layout at each call site (same posture as the "
        ++ "`secf_be_to_le` row). ⚠️ Was invisible to the coverage census because the "
        ++ "theorem is `…Frame_spec`: stripping `_spec` gives "
        ++ "`secf_reduce_once_frame`, not a linked symbol (#12568). Lives in "
        ++ "`Codegen/Programs/Secp256k1FieldReduceOnceSAsm.lean`"),
  routine "secf_reduce_once_n" .proven (some "secfReduceOnceNFrame_spec")
      (notes := "the mod-n sibling: whole-routine ABI contract at "
        ++ "`GuestAddrs.secf_reduce_once_n` over `secfReduceOnceNCr`, the same "
        ++ "four-way caller∪callee union with `secfReduceOnceN_prog` as the self leg. "
        ++ "Byte-transparency kernel-checked (`… = secfReduceOnceN_prog := rfl`). "
        ++ "Same conditional-single-reduction shape and the same non-total "
        ++ "disjointness domain as `secf_reduce_once` above. ⚠️ Its module also holds "
        ++ "`cpsBranchWithin` fragments at `+16`/`+108` — those are INTERNAL arm "
        ++ "pieces, not the whole-routine claim; this row cites the frame theorem at "
        ++ "offset 0. ⚠️ WORST MANGLING OF THE CLASS: `secfReduceOnceNFrame` "
        ++ "camel-snakes to `secf_reduce_once_nframe` because the `N` does not "
        ++ "separate from `Frame`, so the census missed it by more than one token "
        ++ "(#12568). Lives in "
        ++ "`Codegen/Programs/Secp256k1FieldReduceOnceNSAsm.lean`"),
  -- The SAME class, one curve over (#12244). `bnf_be_to_le` / `bnf_le_to_be` had
  -- flat contracts in BOTH callers (`…AddModPSAsmStage`, `…MulModPSAsmStage`) and
  -- nowhere else. Measured, not assumed: the two blocks were **byte-identical
  -- modulo the `CodeReq` name** — 186 lines, `addCr` against `mulCr` — which is
  -- the signature of this class, because the union is the only thing that was
  -- ever caller-specific. Both again built the own-`CodeReq` triple internally
  -- via `Fn.retSpecFlat` and widened it with `liftCode` on the very next line, so
  -- naming that step made all four copies one-liners and removed 250 duplicated
  -- lines across the two files. ⭐ The generalisable check: when a `<sym>Flat_spec`
  -- appears in more than one caller, diff the copies modulo the `CodeReq` — if
  -- they agree, the own-`CodeReq` triple already exists inside each of them and
  -- rowing the symbol costs no new proof.
  routine "bnf_be_to_le" .proven (some "bnfBeToLeFlatEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnf_be_to_le` over "
        ++ "`CodeReq.ofProg … bnfBeToLe_prog`, the `GuestImageEntries` pairing: "
        ++ "the 32-byte BIG-ENDIAN buffer at `a0` becomes four LITTLE-ENDIAN u64 "
        ++ "limbs at `a1`. The post is existential in the written BYTES and pins "
        ++ "their decode — `wsNat256 ws' 0 = beBytesToNat inb` — the converter's "
        ++ "whole functional content; the source region is pinned INTACT. Same "
        ++ "both-regions-non-empty geometry as the `secf_be_to_le` row above, so "
        ++ "the same window-disjointness hypothesis `hdisj`: a genuine domain "
        ++ "restriction discharged by the `arenaB`/`arenaM` layout at each call "
        ++ "site, NOT a representability guard, so this triple is not total over "
        ++ "its argument types. ⚠️ Distinct from the two `bnfBeToLeFlat_spec`s that "
        ++ "remain in the caller stage files, anchored over `addCr` / `mulCr` (3 "
        ++ "programs each); those are caller-specific assumptions, not the image "
        ++ "claim, and both are now corollaries of this row's theorem. Lives in "
        ++ "`Codegen/Programs/Bn254FieldConvFlatEntry.lean`"),
  routine "bnf_le_to_be" .proven (some "bnfLeToBeFlatEntry_spec")
      (notes := "the inverse converter, whole-routine triple at "
        ++ "`GuestAddrs.bnf_le_to_be` over `CodeReq.ofProg … bnfLeToBe_prog`: "
        ++ "four LITTLE-ENDIAN u64 limbs at `a0` become a 32-byte BIG-ENDIAN "
        ++ "buffer at `a1`, the post pinning `beBytesToNat ws' = wsNat256 inb 0` "
        ++ "with the source region INTACT. Same both-regions-non-empty geometry "
        ++ "and same `hdisj` domain restriction as its `bnf_be_to_le` twin. ⚠️ Two "
        ++ "further theorems of this name survive in the callers over `addCr` / "
        ++ "`mulCr`; this row cites the own-`CodeReq` one in "
        ++ "`Codegen/Programs/Bn254FieldConvFlatEntry.lean`"),
  -- ⭐ A STALE ALLOWLIST CLAIM, third of this class after `u256_is_zero` (#12283)
  -- and `secf_copy32`. The entry said "no `CodeReq.ofProg (GuestAddrs.<sym>)`
  -- anywhere; anchored through some other base term". The "other base term" is a
  -- file-local abbrev — `msetMemcpyBase : Word := BitVec.ofNat 64
  -- GuestAddrs.mset_memcpy` and `msetMemcpyCode := CodeReq.ofProg msetMemcpyBase
  -- msetMemcpy_prog` — which unfolds to exactly the image pairing. So the claim was
  -- provably FALSE and the symbol was rowable with no new triple. ⚠️ Grade by what
  -- the abbrev UNFOLDS TO, never by the surface term: "anchored through some other
  -- base term" is a statement about spelling, not about the CodeReq.
  routine "mset_memcpy" .proven (some "mset_memcpy_spec_within")
      (notes := "whole-routine triple at `msetMemcpyBase = BitVec.ofNat 64 "
        ++ "GuestAddrs.mset_memcpy` over `msetMemcpyCode = CodeReq.ofProg "
        ++ "msetMemcpyBase msetMemcpy_prog` — byte-for-byte the `GuestImageEntries` "
        ++ "pairing `(GuestAddrs.mset_memcpy, msetMemcpy_prog)`, so this IS the "
        ++ "image claim. `6 * n + 2` steps for an n-byte copy, exiting at "
        ++ "`ra &&& ~~~1`. The post is COMPLETE and deterministic, not existential: "
        ++ "the destination becomes `copyIntoRegion dstBytes srcBytes dstOff srcOff "
        ++ "n`, the SOURCE region is pinned INTACT, `a1`/`a0` advance by exactly n "
        ++ "and the counter `a2` lands at 0. ⚠️ NOT total over its argument types — "
        ++ "eight hypotheses, including 8-BYTE ALIGNMENT of both bases and "
        ++ "`isValidByteAccess` over both windows; these are genuine domain "
        ++ "restrictions. ⚠️ AND, unlike every other row in this block, no LEAN "
        ++ "PROOF currently applies this triple (its docstring names an intended "
        ++ "`selfdestruct_balance_transfer` consumer that does not yet exist), so "
        ++ "satisfiability is not witnessed by use. NB that is a statement about "
        ++ "the triple, NOT about the routine: the machine code IS reached — "
        ++ "`check-rowed-liveness` counts this symbol among the called — so this is "
        ++ "an unused CONTRACT, not dead code. Satisfiability is witnessed "
        ++ "instead: `mset_memcpy_spec_within_nonvacuous` discharges all eight "
        ++ "hypotheses by `decide` at numeric addresses, and "
        ++ "`mset_memcpy_align_bites` is the negative control showing the alignment "
        ++ "premise excludes inputs rather than holding everywhere (#12236/#12195). "
        ++ "⚠️ A SECOND, INDEPENDENT proof of this routine exists — the structured "
        ++ "SAsm `msetMemcpyFn_spec` in `Codegen/Programs/MsetMemcpySAsm.lean`, with "
        ++ "its own byte-tie to `msetMemcpy_prog`; this row cites the FLAT one in "
        ++ "`Codegen/Programs/AccountBalanceHelperSpec.lean`"),
  -- ⭐ THE THIRD SHAPE in this class, and the one my own earlier measurement
  -- GOT WRONG. I graded `bnq_zero` "adjacency CodeReq, no own-CodeReq sibling —
  -- needs the sibling before a row is honest", i.e. real proof work. Half right:
  -- there is indeed no separately NAMED sibling, but `Bn254Fq12SetOneSAsm`'s
  -- `bnqZeroFlat_spec` builds the own-`CodeReq` triple internally via
  -- `Fn.retSpecFlat` and widens it with `liftCode (cr' := bnqCr)` on the next
  -- line — exactly like the converter pairs. So it was free after all.
  -- ⚠️ "No own-CodeReq sibling" is about the NAMES; look for the intermediate
  -- STEP inside the caller's proof before concluding a lift must be built.
  routine "bnq_zero" .proven (some "bnqZeroFlatEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnq_zero` over `bnqZeroCr = "
        ++ "CodeReq.ofProg (GuestAddrs.bnq_zero) bnqZero_prog` — byte-for-byte the "
        ++ "`GuestImageEntries` pairing, so this IS the image claim: the 48-dword "
        ++ "(384-byte) window at `a0` becomes `List.replicate 48 0`, the WHOLE "
        ++ "window, deterministic, not an existential and not a prefix; `a0` ends "
        ++ "advanced past the buffer and `ra` is intact. Derived from the structured "
        ++ "`bnqZeroFn_spec` by `Fn.retSpecFlat`, no hand-written loop proof. Domain: "
        ++ "ABI only (`RwRegion.wf ⟨dst, 384⟩`, `vs.length = 48`, aligned `ra`), so "
        ++ "this one IS total over its argument type — `rw` is the only live window, "
        ++ "hence no disjointness side condition, unlike the converter rows above. "
        ++ "⚠️ NAME COLLISION of the `blq_zero` kind: "
        ++ "`Bn254Fq12SetOneSAsm.bnqZeroFlat_spec` agrees on entry, exit, pre and "
        ++ "post but is anchored over the ADJACENCY `CodeReq` `CodeReq.ofProg "
        ++ "(GuestAddrs.bnq_zero) (bnqZero_prog ++ bnqSetOne_prog)` — a contiguity "
        ++ "claim about TWO routines, strictly stronger than the single-program image "
        ++ "pairing, so NOT rowable as this symbol's claim. It is now a one-line "
        ++ "corollary; note its lift is PREFIX containment, not a union. This row "
        ++ "cites the one in `Codegen/Programs/Bn254Fq12ZeroSAsm.lean`"),
  -- #12568: the BN254 twin of `blq_set_one`, and invisible for the same three
  -- reasons — `…Frame_spec` name, entry spelled as an offset from the sibling, and a
  -- two-program CodeReq. All three resolve the same way; see the `blq_set_one` row.
  routine "bnq_set_one" .proven (some "bnqSetOneFrame_spec")
      (notes := "whole-routine ABI contract for `bnq_set_one` at its guest address, "
        ++ "spelled `(GuestAddrs.bnq_zero + 24)` — equal to `GuestAddrs.bnq_set_one` "
        ++ "by `decide` (0x80034a0c + 24 = 0x80034a24). Over `bnqCr = CodeReq.ofProg "
        ++ "(GuestAddrs.bnq_zero) (bnqZero_prog ++ bnqSetOne_prog)`: the CALLER∪CALLEE "
        ++ "map, since this routine's body calls `bnq_zero` — correct for the CALLER, "
        ++ "whereas the same CodeReq would over-assume for the callee. Contiguity is "
        ++ "`#guard`-checked in the module (`bnq_zero + 4 * bnqZero_prog.length = "
        ++ "bnq_set_one`), so the concatenation is exactly the two `GuestImageEntries` "
        ++ "pairings side by side. Byte-transparency kernel-checked via `setOneProg_eq "
        ++ ":= rfl`. POST: the FQ12 window at the entry `a0` holds ONE — dword 0 = 1 "
        ++ "and dwords 1–71 = 0, the WHOLE 72-dword window deterministically — `a0` "
        ++ "ends at `dst + 576`, and `sp`/`ra`/`s0` are restored to ENTRY values. "
        ++ "Domain: ABI only (`vs.length = 72`, `RwRegion.wf ⟨dst, 576⟩`, aligned "
        ++ "`ra`) — total over its argument types. "
        ++ "⚠️ Same INVISIBILITY as `blq_set_one` (#12568): the theorem is `…Frame_spec`, so the coverage census strips `_spec` and lands on `…_frame`, which is not a linked symbol. The #12580 namespace rule does NOT catch this variant — there the symbol is a SUFFIX of the stripped name, here it is a PREFIX (an extra trailing component). NO NEW PROOF: the theorem already existed. "
        ++ "Lives in `Codegen/Programs/Bn254Fq12SetOneSAsm.lean`"),
  -- ==========================================================================
  -- The FRAME-PORT family (#12244). Four call-frame leaves whose flat triples
  -- have existed since the FramePort work; `proof-frontier.py --shape` grades all
  -- four whole-routine, each over its OWN `CodeReq.ofProg (GuestAddrs.<sym>)
  -- <sym>_prog` with a matching `GuestImageEntries` pairing, and each with a
  -- `<sym>_byte_tie : body ++ [JALR x0 x1 0] = <sym>_prog := by rfl`.
  --
  -- ⚠️ THE ALLOWLIST STILL CALLED THEM TIER B ("needs Fn.retSpecFlat first"),
  -- which was false: there is no `Fn` here at all, the triples are hand-built
  -- straight-line compositions. Same stale-tier-column trap that file warns about.
  --
  -- ⛔ READ THE OVERFLOW NOTES BELOW BEFORE CITING THESE AS SAFETY PROPERTIES.
  -- All four are TOTAL over `depth` — there is no bound hypothesis anywhere — so
  -- they faithfully describe WRAPPING arithmetic and, for the save/load pair,
  -- slot ALIASING at large depth. They are correctness claims about what the
  -- instructions do, NOT proofs that the frame array is used in bounds.
  routine "frame_depth_push" .proven (some "frameDepthPush_spec")
      (notes := "whole-routine triple at `GuestAddrs.frame_depth_push` over "
        ++ "`frameDepthPushCr = CodeReq.ofProg … frameDepthPush_prog`, the "
        ++ "`GuestImageEntries` pairing, 6 steps, exiting at `ra` (aligned). "
        ++ "Complete deterministic post: materialises `&evm_call_depth` into `t0`, "
        ++ "loads the depth, and stores `depth + 1` BOTH to `a0` and back to the "
        ++ "global dword; `ra` preserved. ⚠️ `depth + 1` is WRAPPING `Word` "
        ++ "addition — no overflow guard and no depth-limit check. The triple is "
        ++ "total over `depth`, so at `depth = 2^64 - 1` it says the counter wraps "
        ++ "to 0, which is what `ADDI` does. Do NOT cite this row as evidence of a "
        ++ "call-depth bound; that obligation lives elsewhere. Byte-tied by "
        ++ "`frameDepthPush_byte_tie` (`rfl`). Lives in "
        ++ "`Codegen/Programs/FrameDepthPushSAsm.lean`"),
  routine "frame_depth_pop" .proven (some "frameDepthPop_spec")
      (notes := "the inverse counter leaf, whole-routine triple at "
        ++ "`GuestAddrs.frame_depth_pop` over its own `CodeReq.ofProg`, 6 steps: "
        ++ "`depth - 1` to both `a0` and the `evm_call_depth` global, `ra` "
        ++ "preserved. ⚠️ WRAPPING subtraction with no underflow guard — total over "
        ++ "`depth`, so at `depth = 0` it says the counter wraps to `2^64 - 1`. "
        ++ "That is faithful to `ADDI -1`, and it means this row is NOT a proof "
        ++ "that pops are balanced against pushes. Byte-tied by "
        ++ "`frameDepthPop_byte_tie` (`rfl`). Lives in "
        ++ "`Codegen/Programs/FrameDepthPopSAsm.lean`"),
  routine "frame_save_regs" .proven (some "frameSaveRegs_spec")
      (notes := "whole-routine triple at `GuestAddrs.frame_save_regs` over its own "
        ++ "`CodeReq.ofProg`, 7 steps: writes `a1` (pc) and `a2` (code base) to the "
        ++ "two dwords at `slot = frame_save_area + (depth <<< 4)`, leaving `t0 = "
        ++ "slot`, `t1 = depth <<< 4`, and `a0`/`a1`/`a2`/`ra` intact. Complete "
        ++ "deterministic post over BOTH dwords — a full 16-byte slot write, not a "
        ++ "prefix. ⚠️ NO BOUND ON `depth`: `depth <<< 4` is a WORD shift, so a "
        ++ "large `depth` wraps and the slot can ALIAS other memory. The triple is "
        ++ "total over `depth` and is honest about that — the two `↦ₘ` cells it "
        ++ "owns are named by the computed `slot`, whatever that is. So this row "
        ++ "does NOT establish that the frame array is indexed in bounds. Byte-tied "
        ++ "by `frameSaveRegs_byte_tie` (`rfl`). Lives in "
        ++ "`Codegen/Programs/FrameSaveRegsSAsm.lean`"),
  routine "frame_load_regs" .proven (some "frameLoadRegs_spec")
      (notes := "the reader of the same slot, whole-routine triple at "
        ++ "`GuestAddrs.frame_load_regs` over its own `CodeReq.ofProg`, 7 steps: "
        ++ "loads the two dwords at `slot = frame_save_area + (depth <<< 4)` into "
        ++ "`a0` (pc) and `a1` (code base), and PRESERVES both dwords — a read-only "
        ++ "effect on memory, unlike its `frame_save_regs` twin. `t0 = slot`, `t1 = "
        ++ "depth <<< 4`, `ra` intact. ⚠️ Same unbounded `depth` and therefore the "
        ++ "same aliasing caveat as the twin; total over `depth`. Byte-tied by "
        ++ "`frameLoadRegs_byte_tie` (`rfl`). Lives in "
        ++ "`Codegen/Programs/FrameLoadRegsSAsm.lean`"),
  -- ==========================================================================
  -- The P-256 family (#12244). Four leaves, all four ALREADY carrying flat
  -- triples over their own `CodeReq.ofProg (GuestAddrs.<sym>) <sym>_prog` with
  -- matching `GuestImageEntries` pairings.
  --
  -- ⚠️ A SECOND FLAVOUR OF STALE TIER-B REASON, distinct from the frame family's.
  -- The frame entries claimed "needs Fn.retSpecFlat" when there was no `Fn` at
  -- all. Here there IS an `Fn` — and `Fn.retSpecFlat` had ALREADY BEEN APPLIED,
  -- producing the `…Flat_spec` these rows cite. The entries pointed at the
  -- structured `…Fn_spec` and never noticed its flat sibling in the same file.
  -- `p256_lt_be`'s entry was plainly wrong in a third way: it called
  -- `p256LtBe_spec` a "structured SAsm spec" when that theorem is a flat triple
  -- with an INLINE own `CodeReq.ofProg`.
  -- ⭐ So: cite the theorem you actually read, and read the whole file.
  routine "p256_be_to_le" .proven (some "p256BeToLeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.p256_be_to_le` over "
        ++ "`p256BeToLeCr = CodeReq.ofProg … p256BeToLe_prog`, the "
        ++ "`GuestImageEntries` pairing: the 32-byte BIG-ENDIAN buffer at `a0` "
        ++ "becomes four LITTLE-ENDIAN u64 limbs at `a1`. The post is the named "
        ++ "`p256BeToLeOutput`, existential in the written BYTES and pinning their "
        ++ "decode `wsNat256 out 0 = beBytesToNat inBytes` — the converter's whole "
        ++ "functional content; the source region is pinned INTACT. Same "
        ++ "both-regions-non-empty geometry as the `secf`/`bnf` converter rows, "
        ++ "hence the same window-disjointness hypothesis `hdisj`: a genuine domain "
        ++ "restriction, NOT a representability guard, so this triple is not total "
        ++ "over its argument types. Also carries a `decide`-able step-size bound "
        ++ "`hsz` left abstract. Lives in `Codegen/Programs/P256BeToLeSAsm.lean`"),
  routine "p256_le_to_be" .proven (some "p256LeToBeFlat_spec")
      (notes := "the inverse converter, whole-routine triple at "
        ++ "`GuestAddrs.p256_le_to_be` over its own `CodeReq.ofProg`: four "
        ++ "LITTLE-ENDIAN u64 limbs at `a0` become a 32-byte BIG-ENDIAN buffer at "
        ++ "`a1`, source pinned INTACT. ⚠️ Its post pins the value in the "
        ++ "`Accel.leLimbsToNat [wsDword inBytes 0, …, wsDword inBytes 24]` form "
        ++ "rather than the `wsNat256 inBytes 0` form its `secf`/`bnf` counterparts "
        ++ "use — the two are equal by `rfl`, but the ROWED statement is the "
        ++ "`leLimbsToNat` one, so quote it that way. Same both-windows geometry and "
        ++ "the same `hdisj` domain restriction as its twin. Lives in "
        ++ "`Codegen/Programs/P256LeToBeSAsm.lean`"),
  routine "p256_copy_n" .proven (some "p256CopyNFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.p256_copy_n` over its own "
        ++ "`CodeReq.ofProg`, parameterised by the length `len`. ⭐ STRONGER POST "
        ++ "THAN THE CONVERTERS: not existential at all — the destination becomes "
        ++ "exactly `bs.take len` and the source region is pinned INTACT, so the "
        ++ "full effect is deterministic. Domain: `orig.length = len`, `len ≤ "
        ++ "bs.length`, both bases non-overflowing, and `hdisj` (two live windows "
        ++ "again). Note `len` is a `Nat` passed in `a2` as `BitVec.ofNat 64 len`, "
        ++ "so the triple says nothing about `len ≥ 2^64` inputs — they are outside "
        ++ "the domain rather than mis-specified. Lives in "
        ++ "`Codegen/Programs/P256CopyNSAsm.lean`"),
  routine "p256_lt_be" .proven (some "p256LtBe_spec")
      (notes := "whole-routine triple at `ltPBase = GuestAddrs.p256_lt_be` over an "
        ++ "INLINE `CodeReq.ofProg ltPBase p256LtBe_prog` (no named abbrev — which "
        ++ "is why the allowlist mis-read it as structured), 296 steps over a "
        ++ "16-instruction program. ⭐ GENUINE NUMERIC POST, the strongest shape in "
        ++ "this batch: `a0` becomes `if beBytesToNat xs < beBytesToNat bs then 1 "
        ++ "else 0` — the REAL strict less-than of the two 32-byte big-endian "
        ++ "operands, not a per-byte or per-limb surrogate (big-endian "
        ++ "lexicographic order IS numeric order). Both input regions untouched, "
        ++ "`a1` preserved, and only `t0`/`t1`/`t2`/`t3`/`t4` owned rather than the "
        ++ "whole exposed file — a more precise footprint than the `regOwns "
        ++ "exposedRegs` rows. Domain: both operands 32 bytes, both bases 8-ALIGNED, "
        ++ "non-overflowing, and `isValidByteAccess` over both windows — real "
        ++ "restrictions, so not total over its argument types. Lives in "
        ++ "`Codegen/Programs/P256LtBeSAsm.lean`"),
  -- ==========================================================================
  -- The BLS12 LEAF family (#12244). Eight routines in three shapes, all already
  -- flat over their own `CodeReq.ofProg (GuestAddrs.<sym>) <sym>_prog` with
  -- matching `GuestImageEntries` pairings, all derived by `Fn.retSpecFlat`.
  --
  -- ⚠️ THE `frameOk*` PREDICATES ARE THE `hdisj` DOMAIN RESTRICTION UNDER A NAME.
  -- `frameOk96` / `frameOk576` / `frameOk1728` / `frameOkN` all unfold to the same
  -- three conjuncts: both bases non-overflowing AND the two windows disjoint. So
  -- the four COPIERS are not total over their argument types, exactly like the
  -- converter rows — the name just hides it. The two ZEROERS have a single live
  -- window and therefore ARE total.
  --
  -- ⛔ TWO RESULT-FUNCTION NAME COLLISIONS. `fq12IsZeroResult` is defined in BOTH
  -- `Bls12Fq12IsZeroSAsm.lean` (OR-fold over 72 dwords) and
  -- `Bn254Fq12IsZeroSAsm.lean` (over 48) — same name, different curve, different
  -- width. `isZeroNResult` is likewise in both `Bls12G1IsZeroNSAsm.lean` and
  -- `P256IsZeroNSAsm.lean` with identical bodies. Cite the namespace, never the
  -- bare name.
  routine "blq_copy" .proven (some "blqCopyFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blq_copy` over `blqCopyCr = "
        ++ "CodeReq.ofProg … blqCopy_prog`, the `GuestImageEntries` pairing. "
        ++ "DETERMINISTIC post, not existential: the 576-byte window at `a1` becomes "
        ++ "exactly `srcBytes` and the SOURCE region is pinned INTACT — a full Fq12 "
        ++ "element copy. Domain: `frameOk576 src dst`, which unfolds to both bases "
        ++ "non-overflowing plus window DISJOINTNESS, so this is NOT total over its "
        ++ "argument types; the overlapping case is outside the domain rather than "
        ++ "handled (contrast `mset_memcpy`, also non-overlap-only, and MCOPY, which "
        ++ "IS overlap-aware). Lives in `Codegen/Programs/Bls12Fq12CopySAsm.lean`"),
  routine "blq_pt_copy" .proven (some "blqPtCopyFlat_spec")
      (notes := "the widest copier in the family: whole-routine triple at "
        ++ "`GuestAddrs.blq_pt_copy` over its own `CodeReq.ofProg`, moving 1728 "
        ++ "bytes (a projective Fq12 point = three 576-byte coordinates). Same "
        ++ "deterministic shape as `blq_copy` — destination becomes exactly "
        ++ "`srcBytes`, source pinned INTACT — and the same disjointness domain via "
        ++ "`frameOk1728`. Lives in `Codegen/Programs/Bls12PtCopySAsm.lean`"),
  routine "blsg_copy96" .proven (some "blsgCopy96Flat_spec")
      (notes := "the G1-point copier, 96 bytes, whole-routine triple at "
        ++ "`GuestAddrs.blsg_copy96` over its own `CodeReq.ofProg`; deterministic "
        ++ "post (`dst` becomes exactly `srcBytes`, source INTACT), disjointness "
        ++ "domain via `frameOk96`. Lives in "
        ++ "`Codegen/Programs/Bls12G1Copy96SAsm.lean`"),
  routine "blsf_copy_quads" .proven (some "blsfCopyQuadsFlat_spec")
      (notes := "the LENGTH-PARAMETERISED copier: whole-routine triple at "
        ++ "`GuestAddrs.blsf_copy_quads` over its own `CodeReq.ofProg`, moving `8 * "
        ++ "n` bytes for `n` dwords passed in `a2`. Deterministic post, source "
        ++ "INTACT, disjointness domain via `frameOkN src dst n`. ⚠️ `n` is a `Nat` "
        ++ "materialised as `BitVec.ofNat 64 n`, so inputs with `n ≥ 2^64` are "
        ++ "outside the domain rather than mis-specified — the same caveat as the "
        ++ "`p256_copy_n` row. Lives in "
        ++ "`Codegen/Programs/Bls12FieldCopyQuadsSAsm.lean`"),
  -- #12568: third member of the `…Frame_spec` invisible class. Unlike the two
  -- set_one routines this one needs NO offset arithmetic — its entry is spelled
  -- `GuestAddrs.blsg2_copy192` directly — and its CodeReq is an explicit two-way
  -- union rather than a concatenation, which the module labels "Non-adjacent
  -- caller/callee code requirement". Only the theorem NAME hid it.
  routine "blsg2_copy192" .proven (some "blsg2Copy192Frame_spec")
      (notes := "whole-routine ABI contract at `GuestAddrs.blsg2_copy192` over "
        ++ "`copy192Cr = (CodeReq.ofProg (GuestAddrs.blsg2_copy192) "
        ++ "blsg2Copy192_prog).union (CodeReq.ofProg (GuestAddrs.blsf_copy_quads) "
        ++ "blsfCopyQuads_prog)` — an explicit CALLER∪CALLEE union of two `ofProg`s at "
        ++ "REAL guest addresses (the module calls it the non-adjacent caller/callee "
        ++ "requirement), so this IS the image claim; the callee `blsf_copy_quads` is "
        ++ "itself rowed. Byte-transparency kernel-checked: `copy192Prog_eq : "
        ++ "abiFrameProg (-16) (16) copy192Frame copy192Body = blsg2Copy192_prog := "
        ++ "rfl`. Copies the 192-byte BLS12-381 G2 point via the 24-quad callee; "
        ++ "`sp`/`ra`/`s0` restored to ENTRY values. "
        ++ "⚠️ Same INVISIBILITY as `blq_set_one` (#12568): the theorem is `…Frame_spec`, so the coverage census strips `_spec` and lands on `…_frame`, which is not a linked symbol. The #12580 namespace rule does NOT catch this variant — there the symbol is a SUFFIX of the stripped name, here it is a PREFIX (an extra trailing component). NO NEW PROOF: the theorem already existed. "
        ++ "⭐ Note this one needed NO offset arithmetic (its entry is spelled at its "
        ++ "own symbol) and NO adjacency reasoning (its CodeReq is a union, not a "
        ++ "concatenation) — the theorem NAME was the entire reason it was uncounted. "
        ++ "Lives in `Codegen/Programs/Bls12G2Copy192SAsm.lean`"),
  routine "blsg_zero96" .proven (some "blsgZero96Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg_zero96` over its own "
        ++ "`CodeReq.ofProg`: the 96-byte window at `a0` becomes `List.replicate 96 "
        ++ "0` — the WHOLE window, deterministic, not a prefix. ⭐ TOTAL over its "
        ++ "argument type: `rw` is the only live window, so there is no "
        ++ "disjointness side condition and no `frameOk*` — ABI hypotheses only "
        ++ "(`RwRegion.wf ⟨dst, 96⟩`, `orig.length = 96`, aligned `ra`). Same shape "
        ++ "as the `bnq_zero` / `blq_zero` rows. Lives in "
        ++ "`Codegen/Programs/Bls12G1Zero96SAsm.lean`"),
  routine "blsg2_zero192" .proven (some "blsg2Zero192Flat_spec")
      (notes := "the G2 zeroer, 192 bytes, whole-routine triple at "
        ++ "`GuestAddrs.blsg2_zero192` over its own `CodeReq.ofProg`; post is "
        ++ "`List.replicate 192 0` over the whole window and, like its G1 twin, the "
        ++ "triple IS total over its argument type. Lives in "
        ++ "`Codegen/Programs/Bls12G2Zero192SAsm.lean`"),
  routine "blq_is_zero" .proven (some "blqIsZeroFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blq_is_zero` over its own "
        ++ "`CodeReq.ofProg`: `a0` becomes `fq12IsZeroResult bs`, the source region "
        ++ "is pinned INTACT (read-only), and only `blqIsZeroScratch` is owned "
        ++ "rather than the whole exposed file — a more precise footprint than the "
        ++ "copier rows. ⚠️ THE POST IS STATED IN IMPLEMENTATION TERMS: "
        ++ "`fq12IsZeroResult bs = if BitVec.ult (fq12OrPrefix bs 72) 1 then 1 else "
        ++ "0`, i.e. the OR-FOLD the code itself computes over 72 dwords, tested "
        ++ "against `< 1`. That is semantically all-limbs-zero (an OR is 0 exactly "
        ++ "when every disjunct is), but it is NOT phrased as `∀ b ∈ bs, b = 0`, so "
        ++ "a spec-level correspondence still has to bridge the fold. ⛔ AND "
        ++ "`fq12IsZeroResult` COLLIDES with a same-named definition in "
        ++ "`Bn254Fq12IsZeroSAsm.lean` that folds 48 dwords, not 72 — this row means "
        ++ "the `Bls12Fq12IsZeroSAsm` one. Takes `576 ≤ bs.length` (≤, not =). Lives "
        ++ "in `Codegen/Programs/Bls12Fq12IsZeroSAsm.lean`"),
  routine "blsg_is_zero_n" .proven (some "blsgIsZeroNFlat_spec")
      (notes := "the length-parameterised is-zero scan, whole-routine triple at "
        ++ "`GuestAddrs.blsg_is_zero_n` over its own `CodeReq.ofProg`: `a0` becomes "
        ++ "`isZeroNResult bs len`, source pinned INTACT, and `a1` is CLOBBERED (it "
        ++ "appears as `regOwn .x11` in the post, having carried `len` in the pre). "
        ++ "⭐ Cleaner post than its Fq12 sibling: `isZeroNResult bs len = if nlz bs "
        ++ "len = len then 1 else 0`, i.e. the leading-zero count over the first "
        ++ "`len` bytes equals `len` — a genuine all-zero characterisation rather "
        ++ "than an OR-fold surrogate. ⛔ `isZeroNResult` COLLIDES with an "
        ++ "identically-bodied definition in `P256IsZeroNSAsm.lean`; this row means "
        ++ "the `Bls12G1IsZeroNSAsm` one. Domain: `len ≤ bs.length` and `ptr.toNat + "
        ++ "len < 2 ^ 64`. Lives in `Codegen/Programs/Bls12G1IsZeroNSAsm.lean`"),
  -- ==========================================================================
  -- THE LAST NINE of the 25 whole-routine triples verified rowable in #12244.
  --
  -- ⛔ THE WORST NAME COLLISION FOUND SO FAR, and it is in a BASE address:
  -- `ltPBase` is defined FOUR times — `Bls12KzgLtBeSAsm` (= GuestAddrs.blsk_lt_be),
  -- `Bls12G1LtPSAsm` (= blsg_lt_p), `P256LtBeSAsm` (= p256_lt_be) and
  -- `Bn254FieldLtPSAsm` (= bnf_lt_p). Same identifier, four DIFFERENT guest
  -- addresses. A `CodeReq.ofProg ltPBase …` therefore says nothing until you know
  -- which namespace you are in — resolve it, always. `leU64` likewise exists three
  -- times (`Blake2fLoadLe64SAsm`, `BalGasValidU64SAsm`, `SSZ/Decode/ChainIdSAsm`,
  -- the last with a different arity).
  --
  -- ⚠️ AND A REPEAT OF THE frame_save_regs HAZARD: two of these index a global array
  -- by an UNBOUNDED shifted register, so their triples describe aliasing rather
  -- than excluding it. Flagged per row.
  routine "bgv_u64le" .proven (some "bgvU64leFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bgv_u64le` over `bgvU64leCr = "
        ++ "CodeReq.ofProg … bgvU64le_prog`, the `GuestImageEntries` pairing: `a0` "
        ++ "becomes `leU64 bs`, the little-endian u64 at the pointer, with the source "
        ++ "region pinned INTACT (read-only) and only `bgvU64leScratch` owned. Domain: "
        ++ "`8 ≤ bs.length` (≤, not =) plus ABI — one live window, so no disjointness "
        ++ "side condition. ⛔ `leU64` is defined THREE times in the tree "
        ++ "(`BalGasValidU64SAsm` here, `Blake2fLoadLe64SAsm`, and "
        ++ "`SSZ/Decode/ChainIdSAsm` with a different arity); this row means the "
        ++ "`BalGasValidU64SAsm` one. Lives in "
        ++ "`Codegen/Programs/BalGasValidU64SAsm.lean`"),
  routine "blk2_ld_le64" .proven (some "blk2LdLe64Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.blk2_ld_le64` over its own "
        ++ "`CodeReq.ofProg`: `a0` becomes `leU64 bytes`, source INTACT. ⚠️ Note this "
        ++ "is the SAME CONTRACT SHAPE as the `bgv_u64le` row above — two distinct "
        ++ "guest routines, each with its own `leU64` definition, computing the same "
        ++ "little-endian dword load. Not a duplication bug (they have separate "
        ++ "addresses and separate images) but a candidate for consolidation, and a "
        ++ "reason never to cite `leU64` unqualified. Domain: `8 ≤ bytes.length`. "
        ++ "Lives in `Codegen/Programs/Blake2fLoadLe64SAsm.lean`"),
  routine "blk2_st_le64" .proven (some "blk2StLe64Flat_spec")
      (notes := "the storing counterpart, whole-routine triple at "
        ++ "`GuestAddrs.blk2_st_le64` over its own `CodeReq.ofProg`: the 8-byte window "
        ++ "at `a0` becomes exactly `dwordBytes value` for the `value` passed in `a1` "
        ++ "— deterministic, whole window. ⭐ TOTAL over its argument types: `rw` is "
        ++ "the only live window, so ABI hypotheses only. Lives in "
        ++ "`Codegen/Programs/Blake2fStoreLe64SAsm.lean`"),
  routine "bloom_or_into" .proven (some "bloomOrIntoFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bloom_or_into` over its own "
        ++ "`CodeReq.ofProg`: the 256-byte bloom filter at `a0` is OR-ed with the one "
        ++ "at `a1`. ⭐ DETERMINISTIC post over the WHOLE window — `dst` becomes "
        ++ "`(List.range 256).map (orByte srcBytes orig)`, i.e. every byte is the OR "
        ++ "of the corresponding pair — with the source pinned INTACT, `a0` returning "
        ++ "0 and `a1` clobbered. Domain: both bases non-overflowing and EXPLICIT "
        ++ "window disjointness `hdisj` (spelled out here rather than hidden behind a "
        ++ "`frameOk*` name, unlike the BLS12 copiers), so not total over its "
        ++ "argument types. ⭐ THE ONLY SYMBOL IN THIS BATCH THAT WAS NEVER "
        ++ "ALLOWLISTED, and the reason is instructive: it already has a row in "
        ++ "`Progress/Correspondence.lean` (#11348), and `check-registry-coverage` "
        ++ "counts EITHER registry as `registered`, so it never needed an "
        ++ "exemption despite having no proof-tier row. The two rows are "
        ++ "COMPLEMENTARY, not duplicates: the correspondence row cites the "
        ++ "STRUCTURED `bloomOrIntoFn_spec` and asserts spec agreement (`.agrees`, "
        ++ "`.bridged`) against `logs_bloom`'s pointwise-OR decomposition in "
        ++ "`SpecRef/BloomAlgebra.lean`; THIS row cites the FLAT "
        ++ "`bloomOrIntoFlat_spec` and asserts a whole-routine triple at the guest "
        ++ "address over its own `CodeReq`. Spec-agreement and machine-triple are "
        ++ "different obligations and a routine needs both. "
        ++ "`check-registry-crosscheck` accepts the pair. Lives in "
        ++ "`Codegen/Programs/BloomOrIntoSAsm.lean`"),
  routine "blsk_lt_be" .proven (some "blskLtBe_spec")
      (notes := "whole-routine triple at `ltPBase = GuestAddrs.blsk_lt_be` over an "
        ++ "inline `CodeReq.ofProg ltPBase blskLtBe_prog`, `len * 9 + 8` steps. "
        ++ "GENUINE NUMERIC POST: `a0` becomes `if beBytesToNat xs < beBytesToNat bs "
        ++ "then 1 else 0` — the real strict less-than of two big-endian operands, "
        ++ "both regions untouched, `a1`/`a2` preserved. ⭐ This is the "
        ++ "LENGTH-PARAMETERISED sibling of the `p256_lt_be` row: same algorithm, and "
        ++ "the step counts agree — `p256_lt_be` is 296 = 32 * 9 + 8, this one is "
        ++ "general in `len`. ⛔ CRITICAL NAMING TRAP: `ltPBase` is defined FOUR times "
        ++ "in the tree, resolving to four DIFFERENT guest addresses "
        ++ "(`blsk_lt_be` here, `blsg_lt_p`, `p256_lt_be`, `bnf_lt_p`), so "
        ++ "`CodeReq.ofProg ltPBase …` is meaningless without its namespace. Domain: "
        ++ "both operands length `len`, both bases 8-ALIGNED, non-overflowing, and "
        ++ "`isValidByteAccess` over both windows. Lives in "
        ++ "`Codegen/Programs/Bls12KzgLtBeSAsm.lean`"),
  routine "bn254_call_allotment" .proven (some "bn254CallAllotment_spec")
      (notes := "whole-routine triple at `allotBase = GuestAddrs.bn254_call_allotment` "
        ++ "over an inline `CodeReq.ofProg`, 13 steps: reads the remaining-gas dword "
        ++ "at `gp + 568` and four stack words at `sp`, and leaves `s6` holding "
        ++ "`bn254Allotment w0 w1 w2 w3 rem`. ALL FIVE memory cells are pinned "
        ++ "UNCHANGED in the post — a pure read plus a register result. ⭐ TOTAL over "
        ++ "its argument types: the only hypothesis is aligned `ra`. ⚠️ `gp + 568` is "
        ++ "a HARDCODED offset into the globals area; the triple names that cell "
        ++ "directly, so it is a claim about that layout and will need revisiting if "
        ++ "the globals block moves. Lives in "
        ++ "`Codegen/Programs/Bn254CallAllotmentSAsm.lean`"),
  routine "dispatcher_capture_exec_state_gas" .proven
      (some "dispatcherCaptureExecStateGas_spec")
      (notes := "whole-routine triple at "
        ++ "`GuestAddrs.dispatcher_capture_exec_state_gas` over `captureCr`, its own "
        ++ "`CodeReq.ofProg`, 9 steps: copies the `evm_state_gas_used` global into "
        ++ "slot `dst = bvgr_tx_exec_state_gas + (index <<< 3)`, leaving `t0 = gas`, "
        ++ "`t1 = dst`, `t2 = ofs` and the source global UNCHANGED. Deterministic "
        ++ "post. ⛔ SAME UNBOUNDED-INDEX HAZARD AS `frame_save_regs`: there is NO "
        ++ "bound on `index`, and `index <<< 3` is a WORD shift, so a large `index` "
        ++ "wraps and the slot can ALIAS other memory. The triple is total over "
        ++ "`index` and honest about it — the `↦ₘ` cell it owns is named by the "
        ++ "computed `dst`, whatever that is — so this row does NOT establish that "
        ++ "the per-tx gas array is indexed in bounds. Lives in "
        ++ "`Codegen/Programs/DispatcherCaptureExecStateGasSAsm.lean`"),
  routine "hp_encode_nibbles" .proven (some "hpEncodeNibblesFlat_spec")
      (notes := "the most semantically meaty row in this batch: whole-routine triple "
        ++ "at `GuestAddrs.hp_encode_nibbles` over its own `CodeReq.ofProg`, computing "
        ++ "the MPT HEX-PREFIX encoding. DETERMINISTIC post — the destination becomes "
        ++ "exactly `hpEncoded srcBytes len isLeaf` and `a0` returns the written "
        ++ "length `1 + len / 2`, with the source nibble buffer pinned INTACT and "
        ++ "`a1`/`a2`/`a3` clobbered. Domain: `len ≤ srcBytes.length`, output window "
        ++ "exactly `1 + len / 2` bytes, both bases non-overflowing, and EXPLICIT "
        ++ "`hdisj` — note the disjointness is ASYMMETRIC in the two window sizes "
        ++ "(`src + len` vs `dst + 1 + len / 2`), so it is not the usual "
        ++ "equal-width form. Not total over its argument types. Lives in "
        ++ "`Codegen/Programs/HpEncodeNibblesSAsm.lean`"),
  routine "mpt_resolve_cache_reset" .proven (some "mptResolveCacheReset_spec")
      (notes := "whole-routine triple at `GuestAddrs.mpt_resolve_cache_reset` over "
        ++ "`cacheResetCr`, its own `CodeReq.ofProg`: zeroes the ENTIRE 32768-byte "
        ++ "resolve cache to `List.replicate 32768 0`, the whole window, "
        ++ "deterministic. ⚠️ Unlike every other row in this batch the window is at a "
        ++ "FIXED global address — `GuestAddrs.mset_res_cache_valid`, not a pointer "
        ++ "argument — so the triple is about that one buffer and takes no base "
        ++ "parameter. `t0` ends owned, `ra` preserved. ⭐ TOTAL over its argument "
        ++ "type (only the 32768 length and ABI hypotheses); one live window, no "
        ++ "disjointness. Step count `2 + (cacheResetFn orig).body.steps + 1` — the "
        ++ "leading 2 is the address materialisation ahead of the loop. Lives in "
        ++ "`Codegen/Programs/MptResolveCacheResetSAsm.lean`"),
  -- ==========================================================================
  -- THE THREE COMPOSITE CALLERS (#12244) — the last of the 28 `--shape`
  -- whole-routine symbols, and the only ones whose `CodeReq` is a UNION.
  --
  -- ⭐ WHY A UNION IS HONEST HERE AND WAS NOT FOR THE LEAVES. For a LEAF (the
  -- `secf`/`bnf` converters, #12389/#12516) the union was an artifact of WHERE the
  -- proof happened to live: the routine needs only its own program loaded, so a
  -- union was a strictly stronger, caller-specific assumption and therefore not
  -- the image claim. For these three the union is SEMANTICALLY REQUIRED — each
  -- body actually `jal`s to its callee, so the routine cannot execute without it —
  -- and the image discharges the union via SEVERAL `GuestImageEntries` pairings
  -- instead of one.
  --
  -- ⚠️ SO THE TEST IS NOT "is it a bare `ofProg`" BUT "is EVERY component a real
  -- image pairing at the address the union names". Verified component-by-component:
  --   encCr  = blsg2_encode  ∪ blsg_le_to_be                      (2/2 pairings)
  --   wireCr = blsk_g2_wire  ∪ blsg_le_to_be                      (2/2 pairings)
  --   addCr  = bnf_add_mod_p ∪ bnf_be_to_le ∪ bnf_le_to_be         (3/3 pairings)
  -- and the calls are real: `jalOff` targets in the emitted bodies are
  -- `blsg_le_to_be`, `blsg_le_to_be`, and (twice) `bnf_be_to_le` plus
  -- `bnf_le_to_be`. A union whose extra components were NOT called would be the
  -- leaf situation again and would not be rowable.
  routine "blsg2_encode" .proven (some "blsg2Encode_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg2_encode` over `encCr`, the "
        ++ "UNION of its own program with its callee `blsg_le_to_be` — required, "
        ++ "because the body `jal`s there, and BOTH components are "
        ++ "`GuestImageEntries` pairings, so the image discharges the whole union. "
        ++ "DETERMINISTIC post over four 48-byte lanes: each becomes "
        ++ "`blsgLeToBeBytes in_i` (the G2 point's four Fp coordinates converted "
        ++ "LE→BE), with all four SOURCE windows pinned INTACT. ⭐ Also a full ABI "
        ++ "FRAME claim, unlike every leaf row: the pre owns the frame slots "
        ++ "(`frameSlotsOwn encFrame`) and the post proves them SAVED and the "
        ++ "callee-saved registers restored (`frameSlotsSaved`), i.e. the routine "
        ++ "honours the calling convention rather than merely computing. Domain: both "
        ++ "bases 8-ALIGNED, `isValidMemAddr` over both 192-byte windows, and window "
        ++ "disjointness — so not total over its argument types. Lives in "
        ++ "`Codegen/Programs/Bls12G2EncodeSAsm.lean`"),
  routine "blsk_g2_wire" .proven (some "blskG2Wire_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsk_g2_wire` over `wireCr`, the "
        ++ "union of its own program with `blsg_le_to_be` (called from the body; both "
        ++ "components are image pairings). Same shape as the `blsg2_encode` row — "
        ++ "four converted 48-byte lanes, sources INTACT, full ABI frame "
        ++ "save/restore. ⚠️ THE WINDOWS ARE ASYMMETRIC: the source is 192 bytes but "
        ++ "the destination is 256, because the KZG wire format interleaves four "
        ++ "16-byte PADDING regions (`p0`..`p3`) between the coordinates. The "
        ++ "disjointness hypothesis is correspondingly asymmetric (`src + 192` vs "
        ++ "`dst + 256`), and the validity hypothesis covers 256 bytes on the "
        ++ "destination side. Not total over its argument types. Lives in "
        ++ "`Codegen/Programs/Bls12KzgG2WireSAsm.lean`"),
  routine "bnf_add_mod_p" .proven (some "bnfAddModP_spec")
      (notes := "the deepest composite in the registry: whole-routine triple at "
        ++ "`GuestAddrs.bnf_add_mod_p` over `addCr`, the union of its own program with "
        ++ "BOTH converters `bnf_be_to_le` and `bnf_le_to_be` — all three components "
        ++ "image pairings, and all three genuinely called (`bnf_be_to_le` TWICE, for "
        ++ "the two operands, then `bnf_le_to_be` for the result). The two converter "
        ++ "rows in this registry are exactly this routine's callees. ⭐ SEMANTIC "
        ++ "POST: existential in the three staging windows, pinning `beBytesToNat "
        ++ "out' = addResult aBE bBE ws` — the real modular sum — plus the arena's "
        ++ "final contents as an explicit triple `setBytes`. ⛔ BUT THE DOMAIN IS THE "
        ++ "HEAVIEST OF ANY ROW HERE, and it is arena-layout-specific: five "
        ++ "parameter-block hypotheses (`hpa`..`hpd`, `hpm`) fixing the CSR-2050 "
        ++ "operand pointers to `arenaB + {0, 0x20, 0x40, 0x80, 0xA0}`, a "
        ++ "modulus-nonzero side condition `wsNat256 ws 0xA0 ≠ 0`, and THREE "
        ++ "disjointness conditions written against LITERAL arena addresses "
        ++ "(0xa0b00e80 / 0xa0b00ea0 / 0xa0b00ec0 / 0xa0b00ee0). Those literals mean "
        ++ "the row is tied to the current arena layout and must be re-checked if "
        ++ "`arenaB` moves — cite it as a layout-conditional claim, not a general one. "
        ++ "Lives in `Codegen/Programs/Bn254FieldAddModPSAsm.lean`"),
  -- ⭐ THE TWO MUL TWINS, recovered from `--shape`'s `needs-read` bucket (#12244).
  -- Both were flagged `needs-read` for one reason only: "ambiguous name(s) mulCr --
  -- defined in >1 file". `mulCr` exists in THREE modules (`AbiFrameLoopDemo`,
  -- `Bn254FieldMulModPSAsmStage`, `Secp256k1FieldMulModPSAsmStage`), so a
  -- name-based grader cannot tell which CodeReq a statement means — the same defect
  -- as `ltPBase`'s four definitions. Resolving `mulCr` PER-MODULE (in the file the
  -- theorem lives in) settles it immediately, and both unions turn out fully
  -- image-backed: 3/3 pairings each, self-anchored first component.
  -- ⇒ `--shape`'s `needs-read` bucket is NOT a residue of hard cases; it is mostly
  -- a residue of AMBIGUOUS NAMES. Resolve per-module before reading a proof.
  routine "bnf_mul_mod_p" .proven (some "bnfMulModP_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnf_mul_mod_p` over `mulCr`, the "
        ++ "union of its own program with BOTH converters `bnf_be_to_le` and "
        ++ "`bnf_le_to_be` — all three `GuestImageEntries` pairings, and the union is "
        ++ "semantically required because the body calls them. The exact structural "
        ++ "twin of the `bnf_add_mod_p` row above: same ABI frame claim "
        ++ "(`frameSlotsOwn` in the pre, `frameSlotsSaved` in the post), same "
        ++ "existential post over the staging windows pinning the arithmetic result, "
        ++ "same CSR-2050 accelerator step with the operand block staged in `arenaB`. "
        ++ "⚠️ INHERITS THE SAME LAYOUT-CONDITIONAL DOMAIN as its ADD twin: "
        ++ "parameter-block hypotheses fixing the operand pointers to fixed `arenaB` "
        ++ "offsets, a modulus-nonzero side condition, and disjointness written "
        ++ "against LITERAL arena addresses — so cite it as a layout-conditional "
        ++ "claim and re-check if the arena moves. ⛔ `mulCr` is one of THREE "
        ++ "definitions of that name; this row means the one in "
        ++ "`Bn254FieldMulModPSAsmStage.lean`. Lives in "
        ++ "`Codegen/Programs/Bn254FieldMulModPSAsm.lean`"),
  routine "secf_mul_mod_p" .proven (some "secfMulModP_spec")
      (notes := "the secp256k1 counterpart: whole-routine triple at "
        ++ "`GuestAddrs.secf_mul_mod_p` over its own `mulCr` — union with "
        ++ "`secf_be_to_le` and `secf_le_to_be`, 3/3 image pairings, both callees "
        ++ "themselves rows in this registry. Same ABI-frame and existential-post "
        ++ "shape as the BN254 twin, and the same layout-conditional domain caveat. "
        ++ "⛔ NOTE THE NAME HAZARD IS DOUBLE HERE: `mulCr` is defined three times, "
        ++ "and the two curves' copies differ ONLY in which converters they union — "
        ++ "so a grader that resolves `mulCr` in the wrong module would silently "
        ++ "attribute BN254 callees to this row. This row means the `mulCr` in "
        ++ "`Secp256k1FieldMulModPSAsmStage.lean`. Lives in "
        ++ "`Codegen/Programs/Secp256k1FieldMulModPSAsm.lean`"),
  -- ==========================================================================
  -- ⭐ A THIRD BLOCKER CLASS, and the first rows in this issue that needed NEW
  -- (if small) proof content rather than re-grading (#12244).
  --
  -- `widx_cmp32_spec` and `widx_record_ptr_spec` were listed tier B, "needs
  -- Fn.retSpecFlat". Wrong twice over: there is no `Fn` and no structured spec at
  -- all, and the triples were ALREADY flat whole-routine `cpsTripleWithin`s. What
  -- actually blocked them was POSITION-INDEPENDENCE: a free `base` over
  -- `CodeReq.ofProg base <the module's own prog>` rather than the image's
  -- `<sym>_prog`. Stating them that way is right (they are reusable at any link
  -- address); it just is not the `GuestImageEntries` claim.
  --
  -- Closed in `Codegen/Proofs/MptWitnessIndexFlatEntry.lean` by instantiating `base`
  -- and identifying the program — `widxCmp32Prog = widxCmp32_prog` by `decide`, and
  -- `widxRecordPtrProg (laHi …) (laLo …) = widxRecordPtr_prog` by `rfl` (⚠️ NOT
  -- `decide`: no `Decidable` instance synthesizes through `laHi`/`laLo`).
  --
  -- ⛔ `widx_swap_records` is the THIRD member of this family and is deliberately
  -- NOT rowed: its `widxSwapProg` and the image's `widxSwapRecords_prog` are
  -- DIFFERENT programs — the proved variant uses `x6` as loop counter where the
  -- image uses `x31` — so no instantiation makes that triple the image claim. The
  -- inequality is kept as a `decide`-checked theorem (`widxSwapProg_ne`) so the
  -- claim cannot rot silently.
  routine "widx_cmp32" .proven (some "widxCmp32Entry_spec")
      (notes := "whole-routine triple at `GuestAddrs.widx_cmp32` over `CodeReq.ofProg "
        ++ "… widxCmp32_prog`, the `GuestImageEntries` pairing, 293 steps: byte-compares "
        ++ "the two 32-byte buffers at `a0`/`a1` and returns a THREE-WAY verdict in "
        ++ "`a0` — `1` if equal, `0` if `as < bs`, `2` otherwise — with both input "
        ++ "regions pinned INTACT. Big-endian lexicographic order IS numeric order, so "
        ++ "this is a genuine comparison, not a per-byte surrogate. ⚠️ Derived from the "
        ++ "position-independent `widx_cmp32_spec` by instantiating its free `base`; the "
        ++ "program identity `widxCmp32Prog = widxCmp32_prog` is `decide`-checked in the "
        ++ "entry module. Domain: both buffers 32 bytes, both bases 8-ALIGNED, "
        ++ "non-overflowing, `isValidByteAccess` over both windows — real restrictions, "
        ++ "so not total over its argument types. Lives in "
        ++ "`Codegen/Proofs/MptWitnessIndexFlatEntry.lean`"),
  routine "widx_record_ptr" .proven (some "widxRecordPtrEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.widx_record_ptr` over "
        ++ "`CodeReq.ofProg … widxRecordPtr_prog`, 7 steps: computes `widx_records + 48 "
        ++ "* a0` into `a0` (as `a0<<<5 + a0<<<4`), clobbering `t0`/`t1` and preserving "
        ++ "every other exposed register. PURE REGISTER ARITHMETIC — no memory "
        ++ "footprint at all, which makes it the only row of that shape here. ⭐ TOTAL "
        ++ "over its argument types: the sole hypothesis is an aligned return address. "
        ++ "⚠️ TWO THINGS TO KNOW BEFORE QUOTING IT. First, the post is the explicit "
        ++ "register-file transformer `widxRecordPtrResult base hi lo rf`, which still "
        ++ "mentions the concrete relocation immediates, so a reader wanting "
        ++ "`= widx_records + 48 * i` must unfold it. Second, the row is only the image "
        ++ "claim because the two link-dependent immediates were instantiated with the "
        ++ "image's OWN `laHi`/`laLo` for `widx_records` relative to "
        ++ "`widx_record_ptr + 12`; the underlying `widx_record_ptr_spec` is "
        ++ "parameterised over them precisely because the data label is layout "
        ++ "dependent. That identity is `rfl`, not `decide` — `Decidable` does not "
        ++ "synthesize through `laHi`/`laLo`. Lives in "
        ++ "`Codegen/Proofs/MptWitnessIndexFlatEntry.lean`"),
  -- ==========================================================================
  -- ⭐ FIRST LIFT OF A `model-only` LEAF (#12244), and the reason the whole bucket
  -- was stuck is NOT what the allowlist says.
  --
  -- The allowlist's remedy for `model-only` is "needs Fn.retSpecFlat". Measured:
  -- that adapter requires `hpostEmp : ∀ rf' ws' A, f.post rf' ws' A → A =
  -- empAssertion`, i.e. the post must DETERMINE the ambient. `Fn.retSpecFlatAmbient`
  -- needs the same thing in the form `hpostAmb : … → A' = A`. So BOTH adapters are
  -- blocked identically, and switching adapters does not help.
  --
  -- ⛔ AND ZERO OF THE 19 linked+image-paired `model-only` leaves pin the ambient:
  -- every one has a post of the shape `fun _ ws _ => …` that ignores its third
  -- argument. So the bucket is blocked on amending the `Fn`s, not on choosing an
  -- adapter. The design contract is visible in `MultiRead.multiReadFn`, whose post
  -- pins `A` to its two read-only inputs, and in `bnqZeroFn`, which pins it to
  -- `empAssertion`.
  --
  -- ⇒ The recipe, worked here end to end: pin the ambient in the loop invariant AND
  -- in `pre`/`post`, thread the extra conjunct through the `vcgen` obligations
  -- (mechanical — six of them here, all destructuring or re-supplying), then apply
  -- `Fn.retSpecFlat` exactly as the zeroer rows do. ⚠️ Reduce `body.size` to a
  -- literal in the `hsz` argument first: a `show` mentioning the routine's arguments
  -- leaves free variables and `decide` refuses.
  routine "bnc_zero64" .proven (some "bncZero64Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnc_zero64` over `bncZero64Cr = "
        ++ "CodeReq.ofProg … bncZero64_prog`, the `GuestImageEntries` pairing: the "
        ++ "64-byte BN254 curve-point buffer at `a0` becomes `List.replicate 64 0` — "
        ++ "the WHOLE window, deterministic, not an existential and not a prefix. "
        ++ "⭐ TOTAL over its argument type: `rw` is the only live window, so ABI "
        ++ "hypotheses only (`RwRegion.wf ⟨dst, 64⟩`, `orig.length = 64`, aligned "
        ++ "`ra`) and no disjointness side condition. ⚠️ THIS ROW REQUIRED CHANGING "
        ++ "`bncZero64Fn` ITSELF, not just adding a lift: its `pre`/`post` (and the "
        ++ "loop invariant `zeroInv`) now PIN the ambient to `empAssertion`, because "
        ++ "`Fn.retSpecFlat`'s `hpostEmp` — and equally "
        ++ "`Fn.retSpecFlatAmbient`'s `hpostAmb` — is unprovable from a post that "
        ++ "ignores its ambient argument. The `Fn` had no callers outside its own "
        ++ "module, so the change is self-contained. Lives in "
        ++ "`Codegen/Programs/Bn254CurveZeroSAsm.lean`"),
  -- ⭐ THE RECIPE APPLIED, twice more — and it transferred without adjustment.
  -- `Secp256k1PointZero64SAsm` is character-identical to `Bn254CurveZeroSAsm` modulo
  -- naming (measured: an 18-line diff, all docstring / one import / two line-wraps),
  -- so the same patch built first try. `Bn254Fp2ZeroSAsm` is the STRAIGHT-LINE member
  -- — eight `SD`s, no loop — so it had no invariant to amend, only the `Fn`'s
  -- pre/post; its post obligation needed the conjunction split instead.
  -- ⚠️ Both were checked for external consumers of their `Fn` BEFORE amending: neither
  -- has any outside its own module. `pre`/`post` are an `Fn`'s API.
  routine "secp256k1_point_zero64" .proven (some "secp256k1PointZero64Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.secp256k1_point_zero64` over "
        ++ "`secp256k1PointZero64Cr = CodeReq.ofProg … secp256k1PointZero64_prog`, the "
        ++ "`GuestImageEntries` pairing: the 64-byte secp256k1 affine-point buffer at "
        ++ "`a0` becomes `List.replicate 64 0` — the WHOLE window, deterministic. "
        ++ "⭐ TOTAL over its argument type (one live window, ABI hypotheses only). "
        ++ "Derived by the #12244 model-only recipe: the ambient is now pinned in "
        ++ "`zeroInv`, `pre` and `post` so `Fn.retSpecFlat`'s `hpostEmp` is provable at "
        ++ "all. Lives in `Codegen/Programs/Secp256k1PointZero64SAsm.lean`"),
  routine "bnp_fp2_zero" .proven (some "bnpFp2ZeroFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnp_fp2_zero` over its own "
        ++ "`CodeReq.ofProg`: zeroes the 64-byte BN254 Fp2 element at `a0` with eight "
        ++ "aligned dword stores. ⚠️ NOTE THE SHAPE DIFFERENCE from its two siblings — "
        ++ "this one is STRAIGHT-LINE, no loop, so the step count is `body.steps + 1` "
        ++ "over an 8-instruction block and there was no loop invariant to amend; only "
        ++ "the `Fn`'s pre/post needed the ambient pinned, and the post obligation "
        ++ "needed its conjunction split rather than a threaded invariant. Post is "
        ++ "COMPLETE and deterministic; ⭐ TOTAL over its argument type. Lives in "
        ++ "`Codegen/Programs/Bn254Fp2ZeroSAsm.lean`"),
  -- ==========================================================================
  -- THE COPIER TRANCHE (#12244), three of five. Same `Fn`-amendment recipe as the
  -- zeroers, with ONE structural difference: `region := ⟨src, srcBytes⟩` is
  -- NON-EMPTY, so the read-only source window rides through `Fn.retSpecFlat` as an
  -- outer conjunct and the `Region.empty` collapse the zeroer lifts use does not
  -- apply.
  --
  -- ⚠️ TWO PER-MODULE GOTCHAS, both caught by asserted anchors rather than by review:
  --   * `Bn254Fp2CopySAsm`'s `pre` lists `orig.length` BEFORE `srcBytes.length`, the
  --     opposite of `Bn254CurveCopySAsm`. A regex-style patch would have silently
  --     swapped two hypotheses of the same type; the assertion caught it twice (once
  --     in the `Fn` edit, once in `hpre`).
  --   * the `post` obligation ends `rw [...]; rfl`, which stops working the moment the
  --     post becomes a conjunction — it needs `exact ⟨by rw [...], hA⟩`.
  --
  -- ⛔ THE OTHER TWO COPIERS ARE A DIFFERENT LOOP SHAPE, not a size variant.
  -- `bnq_copy` (384 B) and `bnq_pt_copy` (1152 B) step by DWORDS — their invariant is
  -- `rf.get .x10 = src + 8 * (i + 1)`, counter in `x7`, bound `i < 48` — where these
  -- three step by bytes with the counter in `x5`. So the byte-stepping patch does not
  -- apply to them and they stay unrowed pending their own anchors.
  routine "bnc_copy64" .proven (some "bncCopy64Flat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnc_copy64` over `bncCopy64Cr = "
        ++ "CodeReq.ofProg … bncCopy64_prog`, the `GuestImageEntries` pairing: copies "
        ++ "the 64 bytes at `a0` to `a1`. DETERMINISTIC post — the destination becomes "
        ++ "exactly `srcBytes` and the SOURCE region is pinned INTACT. ⚠️ NOT total "
        ++ "over its argument types: `frameOk64 src dst` unfolds to both bases "
        ++ "non-overflowing AND the two windows DISJOINT, so the overlapping case is "
        ++ "outside the domain rather than handled — the same named-predicate-hides-"
        ++ "disjointness trap as the BLS12 copier rows. Derived by the #12244 "
        ++ "model-only recipe (ambient pinned in `copyInv`, `pre` and `post`). Lives in "
        ++ "`Codegen/Programs/Bn254CurveCopySAsm.lean`"),
  -- #12319: the FIRST secp256k1 curve-op row, and the first CSRS accelerator site
  -- outside the hash family. ⚠️ NOT a new proof — `pointDouble_spec` already existed
  -- and was simply INVISIBLE to the coverage census: the theorem is named
  -- `pointDouble_spec`, so `check-registry-coverage` strips `_spec` and maps
  -- `pointDouble` → `point_double`, which is not the linked symbol
  -- `secp256k1_point_double` (the `secp256k1` part lives in the MODULE NAMESPACE).
  -- Both gate layers missed it: the strict census drops it at its `sym in symbols`
  -- guard, and the loose backstop only collects names that PREFIX a linked symbol.
  -- Filed separately; unlike #12526 this blind spot hid REAL proven work.
  routine "secp256k1_point_double" .proven (some "pointDouble_spec")
      (notes := "whole-routine triple at `GuestAddrs.secp256k1_point_double` over "
        ++ "`pdCr` — its own `CodeReq.ofProg … secp256k1PointDouble_prog` unioned "
        ++ "with its four callees' (`secf_is_zero32`, `secf_zero32`, "
        ++ "`secf_be_to_le`, `secf_le_to_be`), every leg an `ofProg` at a REAL guest "
        ++ "address, i.e. the standard caller∪callee union (the "
        ++ "`block_hash_from_header` shape). ⚠️ Anchoring over `pdCr` is WRONG for a "
        ++ "callee — the `secf_be_to_le` row calls the `pdCr`-anchored converter "
        ++ "theorems caller-specific assumptions, not the image claim — but CORRECT "
        ++ "here, where those callees are genuinely part of this routine's code map. "
        ++ "Byte-transparency is kernel-checked: `pdProg_tie : abiFrameProg (-32) (32) "
        ++ "pdFrame pdBody = secp256k1PointDouble_prog := rfl`, and the symbol is "
        ++ "paired in `GuestImageEntries`. ⭐ GENUINE DISJUNCTIVE POST, both branches "
        ++ "INSIDE the claim: either `beBytesToNat yBE = 0` and the output is the "
        ++ "64-byte zero point with `a0 = 1` and the staging arena UNTOUCHED, or "
        ++ "`yBE ≠ 0` and `∃ oX' oY'` BE-decoding to the two coordinates of "
        ++ "`Accel.curveDbl Accel.secpP x y` — the accelerator's real affine "
        ++ "TANGENT-DOUBLING semantic, not a stub — with `a0 = 0` and the arena "
        ++ "holding its LE wire image `pairBytes 4 (…)`. The accelerator step is "
        ++ "`CSRS 0x804` (verified from the emitted Program, per #11924), discharged "
        ++ "by `csrs_curveDbl_spec_within`. `sp`/`ra`/`s0`/`s1` restored; inputs "
        ++ "framed; `x0 ↦ᵣ 0` rides through because the branch reads it. ⚠️ NOT total "
        ++ "over its argument types — the arena-disjointness pair `hdIn`/`hdOut` is a "
        ++ "genuine domain restriction discharged by the arena layout at each call "
        ++ "site (same posture as the `secf_be_to_le` row), while `hxlt`/`hylt` "
        ++ "(`beBytesToNat · < Accel.secpP`) are representability guards. ✅ THE PURE "
        ++ "`SpecRef.pointAdd` POINT-ARITHMETIC BRIDGE IS NOW DISCHARGED — #12319 is "
        ++ "no longer a residual on this row. `Crypto/Secp256k1PointArith.lean` "
        ++ "proves the two legs of the SpecRef case split: `pointAdd_self_zero` (at "
        ++ "`y = 0` the point is its own inverse, so the group law returns `𝒪` — "
        ++ "unconditional) and `pointAdd_self_of_ne_zero` (for `0 < y < p` "
        ++ "self-addition IS `Accel.curveDbl`), packaged as the `if`-characterisation "
        ++ "`pointAdd_self`. The only content is the doubling gate "
        ++ "`two_mul_mod_ne_zero`: `p ∣ y + y` with `0 < y + y < 2p` forces "
        ++ "`y + y = p`, which an ODD `p` refuses — primality is NOT used, only "
        ++ "`secpP_odd`. `Codegen/Programs/Secp256k1PointDoubleBridge.lean` then "
        ++ "composes them with this triple as `pointDouble_spec_pointAdd`: the SAME "
        ++ "triple (identical step bound, entry/exit, `pdCr`, precondition and "
        ++ "spatial footprint, proved by `cpsTripleWithin_weaken` with the identity "
        ++ "on the pre) with `Accel.curveDbl` ABSENT from the post — the infinity "
        ++ "branch additionally carries `pointAdd P P = none` and the generic branch "
        ++ "is `∃ q, pointAdd P P = some q` with the output BE-encoding `q` and the "
        ++ "arena holding `pairBytes 4 q`, for "
        ++ "`P = some (beBytesToNat xBE, beBytesToNat yBE)`. No new hypothesis is "
        ++ "introduced, so the derived triple's domain is exactly this one's. "
        ++ "⭐ `pointDouble_spec_pointAdd` is registered as an ADDITIONAL axiom "
        ++ "witness beside `pointDouble_spec`, so the ✅ above is gate-checked "
        ++ "rather than prose: if the bridge regressed or acquired an axiom, "
        ++ "`check-axioms.sh` fails. Registering it as an additional witness "
        ++ "rather than replacing this row's is deliberate — the row's ref is "
        ++ "matched by DOTTED SUFFIX and its census attribution by stripping "
        ++ "`_spec`, and `pointDouble_spec_pointAdd` satisfies neither, so a "
        ++ "swap would orphan the ref AND reintroduce the census blind spot "
        ++ "recorded at the top of this row. "
        ++ "Non-vacuity: `pointAdd_self_gen` instantiates the `0 < y < p` bundle at "
        ++ "the real generator and `pointAdd_self_gen_kat` pins the value to the "
        ++ "independently computed `2·G` (`decide +kernel`), with two NEGATIVE "
        ++ "CONTROLS — `pointAdd_self_ne_curveDbl_of_zero` and "
        ++ "`pointAdd_self_ne_curveDbl_at_p` — exhibiting inputs where `hy0` resp. "
        ++ "`hylt` is provably false AND the conclusion provably fails, so neither "
        ++ "hypothesis is decoration. ⚠️ WHAT IS STILL OPEN (and NOT part of this "
        ++ "row): no whole-routine triple for `secp256k1_point_add` — the chord leg "
        ++ "`pointAdd_of_fst_ne` is proved pure, but `secp256k1PointAdd_prog` "
        ++ "(~80 instructions, 6+ calls) is untouched. Lives in "
        ++ "`Codegen/Programs/Secp256k1PointDoubleSAsm.lean`"),
  routine "secp256k1_point_copy64" .proven (some "secp256k1PointCopy64Flat_spec")
      (notes := "the secp256k1 counterpart, whole-routine triple at "
        ++ "`GuestAddrs.secp256k1_point_copy64` over its own `CodeReq.ofProg`: 64-byte "
        ++ "affine-point copy, deterministic post, source INTACT, same `frameOk64` "
        ++ "disjointness domain. Byte-stepping loop with the counter in `t0`, so the "
        ++ "`bnc_copy64` patch transferred unchanged. Lives in "
        ++ "`Codegen/Programs/Secp256k1PointCopy64SAsm.lean`"),
  routine "bnp_fp2_copy" .proven (some "bnpFp2CopyFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnp_fp2_copy` over its own "
        ++ "`CodeReq.ofProg`: copies the 64-byte BN254 Fp2 element from `a0` to `a1`. "
        ++ "⚠️ STRAIGHT-LINE — sixteen alternating `LD`/`SD` dword pairs, no loop — so "
        ++ "the step count is `body.steps + 1` over a 16-instruction block and there "
        ++ "was no invariant to amend, only the `Fn`'s pre/post. Deterministic post, "
        ++ "source INTACT, `frameOk64` disjointness domain (so not total). ⚠️ This "
        ++ "module's `pre` orders `orig.length` before `srcBytes.length`, the opposite "
        ++ "of `bncCopy64Fn` — relevant to anyone reusing the patch. Lives in "
        ++ "`Codegen/Programs/Bn254Fp2CopySAsm.lean`"),
  -- ⭐ THE COPIER FAMILY IS NOW COMPLETE (5/5, #12244). These last two are the
  -- DWORD-STEPPING variant — a genuinely different loop, not a size variant:
  --   byte-stepping (the three above): `x10 = src + i`,       counter x5, `i ≤ 64`
  --   dword-stepping (these two):      `x10 = src + 8*(i+1)`, counter x7, `i < NDW`
  -- and their `mem` obligation has TWO branches (pre-entry and loop) where the
  -- byte-stepping one has a single `rintro`. So they needed their own anchors; the
  -- byte-stepping patch's invariant assertion refused them both before touching a
  -- line, which is exactly what an asserted anchor is for.
  routine "bnq_copy" .proven (some "bnqCopyFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnq_copy` over `bnqCopyCr = "
        ++ "CodeReq.ofProg … bnqCopy_prog`, the `GuestImageEntries` pairing: copies a "
        ++ "384-byte Fq12 element from `a0` to `a1` in 48 DWORD steps. DETERMINISTIC "
        ++ "post — destination becomes exactly `srcBytes`, SOURCE pinned INTACT. ⚠️ NOT "
        ++ "total: `frameOk384 src dst` unfolds to both bases non-overflowing AND the "
        ++ "windows DISJOINT. ⚠️ Distinct from `Bls12Fq12CopySAsm.blqCopyFlat_spec`, "
        ++ "which is the BLS12 Fq12 copier at the SAME 576-byte width class but a "
        ++ "different curve and address — the two are easy to confuse by name. Lives in "
        ++ "`Codegen/Programs/Bn254Fq12CopySAsm.lean`"),
  routine "bnq_pt_copy" .proven (some "bnqPtCopyFlat_spec")
      (notes := "the widest copier in the registry: whole-routine triple at "
        ++ "`GuestAddrs.bnq_pt_copy` over its own `CodeReq.ofProg`, moving 1152 bytes "
        ++ "(a projective BN254 Fq12 point = three 384-byte coordinates) in 144 dword "
        ++ "steps. Deterministic post, source INTACT, `frameOk1152` disjointness domain "
        ++ "so not total. ⚠️ Note the width: at 1152 bytes the `interval_cases` in the "
        ++ "loop-exit obligation enumerates 144 cases, so this module is the slowest of "
        ++ "the family to elaborate — relevant if the pattern is reused at a larger "
        ++ "width. Lives in `Codegen/Programs/Bn254PtCopySAsm.lean`"),
  -- ==========================================================================
  -- THE IS-ZERO TRANCHE (#12244), two of five, and a THIRD geometry: the writable
  -- window is EMPTY (`rw := RwRegion.empty`, `ws = []`) while the read-only region
  -- carries the input. That is the mirror image of the zeroers, and it means the
  -- flat triple has the input as an outer conjunct and NO writable window at all.
  --
  -- ⭐⭐ THESE TWO ARE THE CLEANEST CONFIRMATION OF THE #12531 DIAGNOSIS. Their BLS12
  -- sibling `Bls12Fq12IsZeroSAsm.blqIsZeroFn` ALREADY pinned the ambient in its
  -- pre/post, and that is exactly why `blq_is_zero` was rowable in an earlier batch
  -- with no `Fn` change at all — while `bnq_is_zero`, the SAME ALGORITHM at a
  -- different width, was not. Same routine shape, same proof structure, and the only
  -- difference in flattenability was whether the post mentioned its ambient.
  -- ⇒ Once amended, the BLS12 module's entire flat-entry section ported to BN254 with
  -- name/width substitution and built first try.
  routine "bnq_is_zero" .proven (some "bnqIsZeroFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnq_is_zero` over "
        ++ "`bnqIsZeroCr = CodeReq.ofProg … bnqIsZero_prog`, the `GuestImageEntries` "
        ++ "pairing: ORs the 48 dword limbs of the 384-byte BN254 Fq12 buffer at `a0` "
        ++ "and returns `a0 = 1` iff the accumulator is zero, with the source region "
        ++ "pinned INTACT (read-only) and NO writable window. ⚠️ The post is stated in "
        ++ "IMPLEMENTATION TERMS — `fq12IsZeroResult bs` is `if BitVec.ult "
        ++ "(fq12OrPrefix bs 48) 1 then 1 else 0`, the OR-fold the code computes — so "
        ++ "it is semantically all-limbs-zero but not phrased as `∀ b ∈ bs, b = 0`; a "
        ++ "spec-level correspondence still has to bridge the fold. ⛔ AND NOTE THE "
        ++ "COLLISION: `fq12IsZeroResult` is ALSO defined in `Bls12Fq12IsZeroSAsm` over "
        ++ "72 limbs, not 48 — this row means the `Bn254Fq12IsZeroSAsm` one. Domain: "
        ++ "`384 ≤ bs.length` (≤, not =) plus ABI. Lives in "
        ++ "`Codegen/Programs/Bn254Fq12IsZeroSAsm.lean`"),
  routine "bnp_fp2_is_zero" .proven (some "bnpFp2IsZeroFlat_spec")
      (notes := "the Fp2 member of the same family: whole-routine triple at "
        ++ "`GuestAddrs.bnp_fp2_is_zero` over its own `CodeReq.ofProg`, ORing the eight "
        ++ "dword limbs of a 64-byte buffer and returning `a0 = 1` iff zero; source "
        ++ "INTACT, empty writable window. Same OR-fold-surrogate caveat as its Fq12 "
        ++ "sibling (`fp2IsZeroResult bs = if BitVec.ult (fp2OrPrefix bs 8) 1 then 1 "
        ++ "else 0`). Domain: `64 ≤ bs.length` plus ABI. Lives in "
        ++ "`Codegen/Programs/Bn254Fp2IsZeroSAsm.lean`"),
  -- ⭐ THE FOURTH SUB-SHAPE, and the pattern held a third time (#12244). This is a
  -- `whileBreak` byte scan — SEVEN vcgen obligations (inv_init, inv_step, exhausted,
  -- guard_exit, break, before.load.mem, post) plus TWO named predicates to amend
  -- (`bnfIsZeroScanInv`, `bnfIsZeroScanPost`), not just the `Fn`'s pre/post.
  -- ⭐ But again the template already existed at the SAME WIDTH: `secf_is_zero32` is
  -- rowed, and `Secp256k1FieldIsZeroSAsm`'s `Fn` AND scan predicates already pinned
  -- the ambient. Measured before porting: the normalised diff between the two spec
  -- proofs was EXACTLY 14 ambient-threading edits and nothing else, each verified to
  -- be its old line plus one ambient token — so the proof body was ported wholesale
  -- rather than hand-edited 14 times, and the flat entry triple came from
  -- `secfIsZero32FlatEntry_spec` in the same `AmbientFree` module.
  routine "bnf_is_zero32" .proven (some "bnfIsZero32FlatEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnf_is_zero32` over "
        ++ "`CodeReq.ofProg … bnfIsZero32_prog`, the `GuestImageEntries` pairing: `a0` "
        ++ "becomes 1 iff the 32-byte buffer at `a0` is all-zero, with the source "
        ++ "region pinned INTACT and NO writable window. ⭐ STRONGER POST SHAPE than "
        ++ "its Fq12/Fp2 cousins: the result is `if nlz bs 32 = 32 then 1 else 0`, a "
        ++ "genuine leading-zero-count characterisation of all-zero, NOT the OR-fold "
        ++ "surrogate `fq12IsZeroResult`/`fp2IsZeroResult` those rows carry — so no "
        ++ "fold has to be bridged for a spec correspondence. Domain: `bs.length = 32` "
        ++ "and `ptr.toNat + 32 < 2 ^ 64` plus aligned `ra`. ⚠️ The lift lives in "
        ++ "`Codegen/Proofs/AmbientFreeFlatTriples.lean` (namespace "
        ++ "`EvmAsm.Codegen.AmbientFree`), NOT in `Bn254Field.lean` where the `Fn` is — "
        ++ "beside its `secf_is_zero32` template, which is the point"),
  -- ⭐ THE SAME SHAPE ONE WIDTH UP, and this time the equivalence was MEASURED rather
  -- than assumed: after amending `bncIsInf64Fn` and its two scan predicates, its spec
  -- proof differs from the 32-byte `bnfIsZero32Fn_spec` in exactly 24 lines, ALL of
  -- them width digits — no structural difference at all. The 14 threading edits were
  -- applied by pattern with asserted occurrence COUNTS (2 where a line appears twice),
  -- which is what makes a by-pattern edit safe on non-unique lines.
  -- ⚠️ Widths were deliberately NOT normalised by substitution when comparing: rewriting
  -- "64" would mangle `Rv64`, `BitVec.ofNat 64` and `2 ^ 64`. Each changed line was
  -- classified instead (ambient-only vs digits-only) — the #12538 lesson applied.
  routine "bnc_is_inf64" .proven (some "bncIsInf64FlatEntry_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnc_is_inf64` over "
        ++ "`CodeReq.ofProg … bncIsInf64_prog`, the `GuestImageEntries` pairing: `a0` "
        ++ "becomes 1 iff the 64-byte BN254 curve-point buffer at `a0` is all-zero — "
        ++ "i.e. the point is the encoding of INFINITY — with the source region pinned "
        ++ "INTACT and no writable window. ⭐ Like `bnf_is_zero32` and unlike the "
        ++ "Fq12/Fp2 pair, the post is `if nlz bs 64 = 64 then 1 else 0`, a genuine "
        ++ "leading-zero-count characterisation rather than an OR-fold surrogate. "
        ++ "⚠️ NOTE WHAT THIS ROW DOES AND DOES NOT SAY about infinity: it proves the "
        ++ "routine detects an ALL-ZERO 64-byte buffer. That the all-zero encoding IS "
        ++ "the point at infinity for this curve representation is a SEPARATE spec-level "
        ++ "fact, not established here. Domain: `bs.length = 64`, `ptr.toNat + 64 < 2 ^ "
        ++ "64`, aligned `ra`. Lives in `Codegen/Proofs/AmbientFreeFlatTriples.lean` "
        ++ "(namespace `EvmAsm.Codegen.AmbientFree`), beside its two same-family "
        ++ "templates"),
  -- ⭐⭐ CREDIT WHERE IT IS DUE, and a correction to how I framed this work: the module
  -- header of `Codegen/Proofs/AmbientFreeFlatTriples.lean` ALREADY recorded this exact
  -- diagnosis, by name, for this routine and two siblings — "`enrgU32leFn`, `spwU32leFn`
  -- and `swsU32leFn` are the same computation as `bahU32leFn` but their posts read
  -- `fun rf _ _ => …`, discarding the ambient binder entirely. Those are unliftable
  -- until their contracts are pinned — a leaf change, not a lift." That was written
  -- before #12244. The contribution here is measuring that it holds for ALL 19 linked
  -- model-only leaves rather than three, and doing the leaf change 13 times.
  routine "enrg_u32le" .proven (some "enrgU32leFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.enrg_u32le` over `enrgU32leCr = "
        ++ "CodeReq.ofProg … enrgU32le_prog`, the `GuestImageEntries` pairing: `a0` "
        ++ "becomes `leU32 bs 0`, the 4-byte LITTLE-ENDIAN load at the pointer, with the "
        ++ "source region pinned INTACT (read-only) and no writable window. Domain: `4 ≤ "
        ++ "bs.length` (≤, not =) plus ABI. ⭐ The lift is `bahU32leFlat_spec` ported: "
        ++ "`bah_u32le` is the SAME COMPUTATION whose `Fn` was already ambient-pinned and "
        ++ "was therefore already rowed, so once `enrgU32leFn`'s contract was pinned the "
        ++ "lift followed with name substitution. ⭐ Its three named siblings "
        ++ "`spw_u32le` / `sws_u32le` / `eph_u32le` are NOW DONE TOO (rows below), and "
        ++ "the reason this row previously gave for deferring them was WRONG: they were "
        ++ "said to need a change to the SHARED `sgLoadU32leFn` (five consumers). They "
        ++ "do not. Each wrapper is its OWN `Fn` that merely had field-wise identical "
        ++ "contents; only the SPEC PROOF delegated. Re-pointing that delegation at "
        ++ "`bahU32leFn` — the already-pinned twin — pins each wrapper with the shared "
        ++ "definition untouched. Lives in "
        ++ "`Codegen/Programs/Eip7702NonceReuseGuardSAsm.lean`"),
  -- ⛔ CORRECTION (#12244): the three rows below were deferred TWICE on the claim that
  -- they required amending the SHARED `sgLoadU32leFn` (consumers: EphU32leSAsm,
  -- SszParentHeaderSAsm, SgLoadU32leSAsm, SszWitnessStateSAsm,
  -- SszPayloadWithdrawalsSAsm). That claim conflated "the spec proof delegates to X"
  -- with "the Fn IS X". `spwU32leFn` / `swsU32leFn` / `ephU32leFn` are three SEPARATE
  -- `Fn` definitions whose fields happened to match `sgLoadU32leFn`'s; the coupling was
  -- only `simpa [thisFn, sgLoadU32leFn] using sgLoadU32leFn_spec`. Since
  -- `BlockAccessListHashSAsm.bahU32leFn` is the same `Fn` with the ambient ALREADY
  -- pinned (same `region`, same `body := sgLoadU32leBody`), each wrapper just
  -- re-delegates to bah. `SgLoadU32leSAsm.lean` is NOT in the diff -- verified, not
  -- asserted -- so the five consumers are untouched and the blast radius was zero.
  -- ⇒ The transferable rule: read what a shared symbol is USED FOR before pricing the
  -- change. A delegated PROOF is not a shared DEFINITION.
  routine "spw_u32le" .proven (some "spwU32leFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.spw_u32le` over `spwU32leCr = "
        ++ "CodeReq.ofProg … spwU32le_prog`, the `GuestImageEntries` pairing: `a0` "
        ++ "becomes `leU32 bs 0`, the 4-byte LITTLE-ENDIAN load at the pointer. Memory "
        ++ "UNTOUCHED — source region pinned INTACT (read-only), EMPTY writable window "
        ++ "(`ws = []`). Domain: `4 ≤ bs.length` (≤, not =), region wf, aligned `ra` — no "
        ++ "input-domain restriction, so total. Same computation and same lift as "
        ++ "`bah_u32le` / `enrg_u32le`; its `Fn` is pinned by re-delegating its spec to "
        ++ "the already-pinned `bahU32leFn`, leaving the shared `sgLoadU32leFn` alone. "
        ++ "Lives in `Codegen/Programs/SszPayloadWithdrawalsSAsm.lean`"),
  routine "sws_u32le" .proven (some "swsU32leFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.sws_u32le` over `swsU32leCr = "
        ++ "CodeReq.ofProg … swsU32le_prog`, the `GuestImageEntries` pairing: `a0` "
        ++ "becomes `leU32 bs 0`. Memory UNTOUCHED (read-only region intact, empty "
        ++ "writable window). Domain: `4 ≤ bs.length` plus ABI; total. Same lift as its "
        ++ "`spw_u32le` sibling, via the already-pinned `bahU32leFn`. Lives in "
        ++ "`Codegen/Programs/SszWitnessStateSAsm.lean`"),
  -- #12318 callee-composition lane, `extract_witness_state_section`. A SECOND
  -- witness for `sws_u32le`, not a replacement: the row above stays exactly as
  -- it was. Per this module's header, `symbol` groups rows rather than keying
  -- them, and this is a per-FRAME companion in the same sense the RLP walk
  -- chain has per-FORM ones.
  --
  -- ⛔ WHY IT EXISTS, and the transferable lesson. `swsU32leFlat_spec` is
  -- `.proven` and total — and still cannot be composed into
  -- `extract_witness_state_section`. Its `swsU32leScratch` frame surrenders
  -- `x29` (`regOwns` in the pre, `regOwns` in the post), and the caller holds
  -- `state_off` in `x29` across its third call. Composing the rowed contract
  -- would leave BOTH stored outputs existential in an unknown word. So a
  -- callee row being `.proven` and ungated is NOT sufficient for composition:
  -- the row's REGISTER FRAME can block it just as effectively as a gate, and
  -- no tier constructor or `gate` string records that.
  --
  -- The strengthening is sound and carries no new domain restriction: the body
  -- (`sgLoadU32leBody`) writes `x5`, `x6` and `x10` and nothing else, which
  -- `swsU32lePres_x29` proves rather than assumes.
  routine "sws_u32le" .proven (some "swsU32lePresFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.sws_u32le` over the SAME "
        ++ "`SszWitnessStateSAsm.swsU32leCr` as the row above — the identical "
        ++ "`guestImageEntries` pairing, so this is the same image claim — with "
        ++ "`x29` pinned through pre and post instead of surrendered to "
        ++ "`regOwns`. Strictly STRONGER than `swsU32leFlat_spec`: same domain "
        ++ "(`4 ≤ bs.length`, region wf, aligned `ra`), same post on `a0` "
        ++ "(`leU32 bs 0`), same untouched read-only region, plus the `x29` "
        ++ "conjunct. `swsU32lePres_byte_tie` is the same `rfl` as the sibling "
        ++ "row's, so the `Fn` emits the linked program and is not a variant of "
        ++ "it. ⚠️ SCOPE: this is the ENABLER for the "
        ++ "`extract_witness_state_section` composition (#12318), not that "
        ++ "composition — the 27-instruction wrapper triple is NOT claimed by "
        ++ "this row and remains open. Lives in "
        ++ "`Codegen/Programs/SszWitnessStateSectionSpec.lean`"),
  routine "eph_u32le" .proven (some "ephU32leFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.eph_u32le` over `ephU32leCr = "
        ++ "CodeReq.ofProg … ephU32le_prog`, the `GuestImageEntries` pairing: `a0` "
        ++ "becomes `leU32 bs 0`. Memory UNTOUCHED (read-only region intact, empty "
        ++ "writable window). Domain: `4 ≤ bs.length` plus ABI; total. Same lift as its "
        ++ "`spw_u32le` / `sws_u32le` siblings, via the already-pinned `bahU32leFn`. "
        ++ "Lives in `Codegen/Programs/EphU32leSAsm.lean`"),
  -- #12244: the LAST plain model-only leaf. Two corrections to my own recorded
  -- measurement of it, both found only by reading the file rather than trusting the
  -- note: (1) I said TWO `Fn`s share the invariants -- false, the second
  -- (`copyLoopFn_spec`) sits inside a `/- ... -/` BLOCK COMMENT at lines 382-459, so 7
  -- of the 22 destructure sites I had counted were dead code; (2) the live edit count
  -- was 28 anchored lines, and every one was mechanical. What WAS true and load-bearing
  -- is the confirmed dead end: pinning only the `Fn`'s pre/post does not work, because
  -- `case post` receives the ambient solely through the strongest-post hypothesis, which
  -- routes across BOTH loop boundaries -- so `copyInv` and `padInv` must each carry
  -- `A = empAssertion` themselves.
  routine "ssz_pack_bytes" .proven (some "sszPackBytesFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.ssz_pack_bytes` over "
        ++ "`sszPackBytesCr = CodeReq.ofProg … sszPackBytes_prog` (22 insn), the "
        ++ "`GuestImageEntries` pairing: copies the first `len` bytes at `a0` into the "
        ++ "window at `a2` and ZERO-PADS to the next 32-byte chunk boundary, so `[a2]` "
        ++ "becomes exactly `packedBytes srcBytes len` (`outLen len` bytes), and `a0` "
        ++ "PUBLISHES the SSZ chunk count `chunkCount len` rather than discarding it. "
        ++ "The SOURCE region is pinned INTACT in the post. ⚠️ Two DIFFERENT register "
        ++ "splits, one per direction, because the contract is asymmetric: the pre pins "
        ++ "three ABI registers (`exposedRegs_split_pack3`, peeling 12 scratch) while the "
        ++ "post knows only `a0` (`exposedRegs_split_pack1`, owning 14) — the "
        ++ "`u256_add_be` published-result shape crossed with the reverse-copy's "
        ++ "three-register pre. ⚠️ NOT total: needs src-dst DISJOINTNESS for the same "
        ++ "arithmetic-`inRw` reason as `swr_rev_le_be` (see that row). Two loops (copy "
        ++ "then pad), each with its own invariant, and BOTH invariants carry the pinned "
        ++ "ambient — required, not stylistic. Lives in "
        ++ "`Codegen/Programs/SszPackBytesSAsm.lean`"),
  -- #12244: the LAST model-only leaf, and the only one whose blocker was a genuinely
  -- SHARED DEFINITION rather than a delegated proof. ⭐ But the blast radius I had
  -- recorded ("`WhileBreakDemo.scanInv` is `Rv64/SAsm` infrastructure") was overstated:
  -- `scanInv` has exactly THREE references in the tree — its own def, `scanNzFn`'s body,
  -- and `p256IsZeroNBody`. Every OTHER external use of that module is of the pure `nlz`
  -- spec function and its lemmas, not the invariant. So it is two consumers, one of them
  -- the demo itself, and pinning it cost FOUR edits there.
  -- ⭐ Mechanics worth reusing: only sites that BUILD an enlarged predicate need editing.
  -- `rcases`/`rintro` patterns tolerate a SHORT list — the final binder absorbs the
  -- remaining conjunction — so p256's own 8-obligation proof needed ZERO edits: its
  -- `rintro` bundled the new tail and its `refine` consumed that same bundle.
  routine "p256_is_zero_n" .proven (some "p256IsZeroNFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.p256_is_zero_n` over "
        ++ "`p256IsZeroNCr = CodeReq.ofProg … p256IsZeroN_prog` (12 insn), the "
        ++ "`GuestImageEntries` pairing: `a0` becomes `isZeroNResult bs len` — `1` iff the "
        ++ "first `len` bytes at the pointer are all zero, else `0`, via the "
        ++ "leading-zero scan (`nlz bs len = len`). Memory UNTOUCHED: non-empty read-only "
        ++ "`region` pinned INTACT, EMPTY writable window (`ws = []`) — the is-zero "
        ++ "geometry. ⚠️ Asymmetric registers so TWO splits: the pre pins `a0` (pointer) "
        ++ "and `a1` (length) via `exposedRegs_split_p256_2`, the post publishes only "
        ++ "`a0` via `exposedRegs_split_p256_1`. TOTAL over its argument types — ABI "
        ++ "hypotheses only (`len ≤ bs.length`, no address wraparound, region wf, aligned "
        ++ "`ra`), and `hsz` is discharged internally rather than taken as a hypothesis. "
        ++ "The shared `WhileBreakDemo.scanInv` is pinned to match, since the ambient must "
        ++ "cross the loop boundary. Lives in "
        ++ "`Codegen/Programs/P256IsZeroNSAsm.lean`"),

  -- ==========================================================================
  -- #12245 flat-block pilot. Eight machine-level strongest-post contracts in
  -- `Codegen/Proofs/FlatBlockPilotSpec.lean`, each with an anti-vacuity `example`
  -- reading a FULLY NUMERIC post (#11906 discipline).
  --
  -- ⚠️ Read the pilot's premise correction before using it to plan more of these.
  -- `shape-census.py`'s "588 flat blocks" does NOT describe the addressable class:
  -- it counts emitted `*Function : String` defs, most not linked into the image,
  -- and "flat" there means only "no conditional branch" — the body may still
  -- contain `jal` calls and ZisK precompile `CSRS`. Measured against
  -- `GuestImageEntries.lean`, the in-image `absent` routines that are loop-free
  -- AND callee-free AND precompile-free number THREE, not ~588. The remaining
  -- `absent` mass is 251 loop-free-WITH-calls (needs callee composition) and 10
  -- precompile-staging leaves (needs `AccelStep`'s `bytesRegion` operand-block
  -- reasoning) — neither is a straight-line symbolic-execution exercise.
  --
  -- ⚠️⚠️ TWO ROW SHAPES BELOW, and the second is easy to misread.
  --   * `wcidx_record_ptr`, `write_sets_discard_tx`, `read_sets_discard_tx` exit
  --     at `ra &&& ~~~1` — ordinary returns, nothing subtle.
  --   * the other FIVE are TAIL-TRANSFER routines whose last instruction is
  --     `j <callee>`, so the contract's exit pc is the CALLEE'S ENTRY, not a
  --     return. The triple is complete and unconditional for the routine's own
  --     instructions — that is why it grades `.proven` — but it says NOTHING
  --     about what the callee computes. `secf_square_mod_p` is proven to set up
  --     `a1 := a0` and transfer to `secf_mul_mod_p`; it is NOT proven to square.
  --     A caller-visible result needs the callee's contract composed on top.
  --     If the maintainer would rather these not carry `.proven`, downgrading
  --     them is a one-line change per row and loses no proof.
  routine "wcidx_record_ptr" .proven (some "wcidxRecordPtrFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.wcidx_record_ptr` over "
        ++ "`CodeReq.ofProg … wcidxRecordPtr_prog`, 7 steps, ordinary return: "
        ++ "`a0` becomes `wcidx_records + (i<<<5 + i<<<4)` and `t0`/`t1` end "
        ++ "holding the two shift terms. Companion `wcidxRecordPtr_stride` proves "
        ++ "`(i<<<5) + (i<<<4) = 48 * i`, i.e. the 48-byte record stride. Memory "
        ++ "untouched. In-degree 3: `wcidx_sift_down`, "
        ++ "`witness_codes_index_build`, `witness_codes_lookup_by_hash_indexed`"),
  routine "wcidx_cmp32" .proven (some "wcidxCmp32Entry_spec")
      (notes := "whole-routine triple at `GuestAddrs.wcidx_cmp32` over "
        ++ "`CodeReq.ofProg … wcidxCmp32_prog`, the `GuestImageEntries` pairing, "
        ++ "293 steps: byte-compares the two 32-byte buffers at `a0`/`a1` and "
        ++ "returns a THREE-WAY verdict in `a0` — `1` if equal, `0` if `as < bs`, "
        ++ "`2` otherwise — with both input regions pinned INTACT. The clone of "
        ++ "`widx_cmp32`: `wcidx_cmp32_spec` transfers the sibling's triple "
        ++ "through the token-identity `wcidxCmp32_prog = widxCmp32Prog` "
        ++ "(decide-checked `wcidxCmp32_prog_eq`), and the entry theorem "
        ++ "instantiates its free `base`. Same domain restrictions as the "
        ++ "sibling: 32-byte buffers, 8-aligned non-overflowing bases, "
        ++ "`isValidByteAccess` windows. Lives in "
        ++ "`Codegen/Proofs/WitnessCodeLookupSpec.lean`"),
  routine "write_sets_discard_tx" .proven (some "writeSetsDiscardTxFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.write_sets_discard_tx`, 10 "
        ++ "steps, ordinary return: zeroes the three cursors "
        ++ "`tx_storage_writes_count` / `tx_storage_writes_overflow` / "
        ++ "`storage_writes_undo_count` from ARBITRARY prior contents, and `t0` "
        ++ "ends at the third address. ⚠️ In-degree 0 — reached only from the "
        ++ "dispatcher, so this discharges no named residual today; rowed because "
        ++ "it is one of the three genuinely straight-line in-image routines"),
  routine "read_sets_discard_tx" .proven (some "readSetsDiscardTxFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.read_sets_discard_tx`, 10 "
        ++ "steps, ordinary return: zeroes `tx_storage_reads_count` / "
        ++ "`tx_account_reads_count` / `tx_code_reads_count` from arbitrary prior "
        ++ "contents. ⚠️ In-degree 0, same caveat as `write_sets_discard_tx`"),
  routine "secf_square_mod_p" .proven (some "secfSquareModPFlat_spec")
      (notes := "⚠️ TAIL-TRANSFER contract, 2 steps: entry "
        ++ "`GuestAddrs.secf_square_mod_p`, EXIT `GuestAddrs.secf_mul_mod_p` — "
        ++ "the exit is the callee's entry, NOT a return. Proves exactly that "
        ++ "`a1 := a0` and control transfers to the multiply; it does NOT prove "
        ++ "squaring. Composing `secf_mul_mod_p`'s contract is what would give a "
        ++ "caller-visible `a^2 mod p`. In-degree 3: `secf_pow_mod_p`, "
        ++ "`secf_sqrt_mod_p`, `secp256k1_recover_r`"),
  routine "secf_square_mod_n" .proven (some "secfSquareModNFlat_spec")
      (notes := "⚠️ TAIL-TRANSFER contract, 2 steps, exit "
        ++ "`GuestAddrs.secf_mul_mod_n` — same shape and same caveat as "
        ++ "`secf_square_mod_p`: the argument shuffle is proven, the squaring is "
        ++ "not. In-degree 1: `secf_pow_mod_n`"),
  routine "derive_withdrawal_requests" .proven
      (some "deriveWithdrawalRequestsFlat_spec")
      (notes := "⚠️ TAIL-TRANSFER contract, 7 steps: entry "
        ++ "`GuestAddrs.derive_withdrawal_requests`, EXIT "
        ++ "`GuestAddrs.stage_system_call`; proves the four-argument shuffle "
        ++ "(`a0 := <predeploy addr>`, `a1..a3 := ` the incoming `a0..a2`) and "
        ++ "the transfer, NOT the system call's effect. In-degree 1: "
        ++ "`derive_block_system_requests`. Also documents in Lean the fact whose "
        ++ "absence produced the #11578 leaf mis-annotation"),
  routine "derive_consolidation_requests" .proven
      (some "deriveConsolidationRequestsFlat_spec")
      (notes := "⚠️ TAIL-TRANSFER contract, 7 steps, exit "
        ++ "`GuestAddrs.stage_system_call` — same shape and caveat as "
        ++ "`derive_withdrawal_requests`, different predeploy address. "
        ++ "In-degree 1: `derive_block_system_requests`"),
  -- #12226 harvest. These seven were sitting in `registry-coverage-allow.txt` as
  -- tier B ("structured SAsm spec only; needs Fn.retSpecFlat first"). That label
  -- came from a theorem-NAME heuristic: `check-registry-coverage.py` grades tier A
  -- by the `_spec_within`/`Flat_spec` suffix, and each of these is a flat triple
  -- whose name merely ends `_spec`. The `--shape` classifier added in #12226 parses
  -- the CONCLUSION instead and found them. Each was then read individually, and each
  -- `(GuestAddrs.<sym>, <sym>_prog)` pair was checked present in `GuestImageEntries`
  -- so the CodeReq is the image's real code, not a detached listing.
  routine "bloom_eq" .proven (some "bloomEq_spec")
      (notes := "whole-routine triple at `GuestAddrs.bloom_eq` over "
        ++ "`CodeReq.ofProg … bloomEq_prog`, 297 steps: the output dword `[a2]` "
        ++ "becomes `1` iff the two 256-byte bloom filters are byte-equal, else "
        ++ "`0`, and `a0 = 0`. BOTH input regions are pinned INTACT in the post. "
        ++ "ABI hyps only (both lengths 256, aligned ra) — no input-domain "
        ++ "condition, so it is total over 256-byte filters"),
  routine "blq_eq" .proven (some "blqEq_spec")
      (notes := "whole-routine triple at `GuestAddrs.blq_eq` over "
        ++ "`CodeReq.ofProg … blqEq_prog`: `a0 = 1` iff the two 576-byte BLS12 "
        ++ "Fq12 elements are byte-equal, else `0`; both regions intact. Step "
        ++ "count is `(blqEqBody …).steps`, not a literal — the body is the "
        ++ "shared 72-dword `DualReadScan` scan. Hyps: `Region.wf` on both "
        ++ "operands, lengths 576, aligned ra. ⚠️ EQUALITY of the byte images, "
        ++ "NOT Fq12 equivalence — no field-level reduction is claimed"),
  routine "bnq_eq" .proven (some "bnqEq_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnq_eq` over "
        ++ "`CodeReq.ofProg … bnqEq_prog`: the BN254 twin of `blqEq_spec` over "
        ++ "384 bytes (48 dwords) — `a0 = 1` iff byte-equal, both regions "
        ++ "intact, same `DualReadScan` body and same `Region.wf` + length + "
        ++ "aligned-ra hyps. ⚠️ Byte equality, not Fq12 equivalence"),
  routine "bnp_fp2_eq" .proven (some "bnpFp2Eq_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnp_fp2_eq` over "
        ++ "`CodeReq.ofProg … bnpFp2Eq_prog`: the 64-byte (8-dword) member of "
        ++ "the same `DualReadScan` family — `a0 = 1` iff the two BN254 Fp2 "
        ++ "elements are byte-equal, both regions intact. ⚠️ Byte equality, not "
        ++ "Fp2 equivalence"),
  routine "blsg2_eq_n" .proven (some "blsg2EqN_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg2_eq_n` over "
        ++ "`CodeReq.ofProg … blsg2EqN_prog`, `n * 8 + 7` steps: `a0 = 1` iff "
        ++ "the two `n`-byte regions are equal, else `0`; both intact. ⭐ The "
        ++ "length is PARAMETRIC (`a2 = n`), so unlike its fixed-width siblings "
        ++ "this row covers every call width. Hyps: both lengths `n`, both "
        ++ "pointers 8-aligned, non-overflow, byte-access validity, aligned ra"),
  routine "frame_base" .proven (some "frameBase_spec")
      (notes := "whole-routine triple at `GuestAddrs.frame_base` over "
        ++ "`CodeReq.ofProg … frameBase_prog`, 6 steps: `a0` becomes "
        ++ "`call_frame_arena + depth * 0x19000`, the frame-arena address for "
        ++ "call depth `depth`. Pure register arithmetic — touches NO memory, so "
        ++ "the only hypothesis is aligned ra. ⚠️ The stride is the literal "
        ++ "`0x19000` in the theorem; it does NOT cite a named layout constant, "
        ++ "so a stride change in the arena layout would not break this proof"),
  routine "u256_min" .proven (some "u256Min_spec")
      (notes := "whole-routine triple at `GuestAddrs.u256_min` over "
        ++ "`CodeReq.ofProg … u256Min_prog`, 308 steps: `[a2]` receives the "
        ++ "32-byte BE minimum of the two operands (selected by "
        ++ "`beBytesToNat as ≤ beBytesToNat bs`), `a0 = 0`, both inputs pinned "
        ++ "INTACT. ⚠️ The post LEAKS scratch: `x5` is left holding the winning "
        ++ "POINTER and `x31` the constant 32, rather than being returned as "
        ++ "`regOwn`. A caller that framed over x5/x31 across this call cannot "
        ++ "use this row as-is. Hyps: lengths 32/32/32, both inputs 8-aligned, "
        ++ "non-overflow, byte-access validity, aligned ra"),
  -- #12659 Stage 2: this is the linked priority-fee BODY, not yet the entry
  -- triple.  Its callee adapters and both status arms are consumed; the
  -- six-instruction stack/prologue prefix at P..P+24 remains a separate
  -- composition obligation and is deliberately not hidden by `.proven`.
  routine "priority_fee_per_gas_eip1559" .partly
      (some "priority_fee_per_gas_eip1559_body_spec")
      (notes := "linked body triple at `GuestAddrs.priority_fee_per_gas_eip1559 + 24` "
        ++ "through `+88`: setup, `u256_sub_be`, the in-place `u256_min` call, "
        ++ "status split, restore and return. The theorem consumes the concrete "
        ++ "subtraction inhabitant and the exact-alias min contract, and states "
        ++ "both success and reject posts. It intentionally does NOT claim the "
        ++ "six-instruction entry prologue at `P..P+24`; an entry-anchored whole-"
        ++ "routine triple is the remaining Stage 2 composition. Lives in "
        ++ "`Codegen/Programs/U256GasPricingSAsm.lean`"),
  -- #12659 Stage 2: entry-anchored all-outcome gas/refund arithmetic triple.
  routine "tx_gas_result_increments" .proven
      (some "tx_gas_result_increments_spec")
      (notes := "whole-routine triple at `GuestAddrs.tx_gas_result_increments` "
        ++ "over its own `CodeReq`: the low-gas error arm and refund-success arm "
        ++ "are both covered, with block/receipt increments, before/after refund, "
        ++ "and the emitted scratch-register outputs stated in the post. The "
        ++ "refund bound is a derived consequence of the emitted min-with-"
        ++ "`before/5` select, not a new precondition. ABI/resource hypotheses "
        ++ "only; no input-domain gate. Lives in "
        ++ "`Codegen/Programs/TxGasResultIncrementsSAsm.lean`"),
  routine "blsg_lt_p" .proven (some "blsgLtP_spec")
      (notes := "whole-routine triple at `GuestAddrs.blsg_lt_p`: `a0 = 1` iff the "
        ++ "48-byte big-endian input is `< beBytesToNat bls12PBytes`, input and the "
        ++ "read-only prime region intact. ABI hyps only (alignment, non-overflow, "
        ++ "byte-access validity, aligned ra). The `la` materialization of "
        ++ "`blsg_p_be` is PROVEN, not assumed"),
  routine "blsg_lt_p" .conditional (some "blsgLtP_spec_specref")
      (gate := "the input is the 48-byte compact SUFFIX of a well-formed EIP-2537 "
        ++ "wire felt — `w.length = 64` and the first 16 bytes zero. Load-bearing, "
        ++ "not decorative: the reference decodes all 64 bytes, so a nonzero pad "
        ++ "byte makes the value ≥ 2^384 > p and the reference rejects, while the "
        ++ "guest scan never reads those bytes and would not. The two sides agree "
        ++ "exactly ON the well-formed felts")
      (notes := "model-facing restatement: `a0` IS the accept/reject indicator of "
        ++ "`SpecRef.Bls12.bytes_to_fq` on the wire felt. ⚠️ PREDICATE agreement "
        ++ "only — `lt_p` returns a boolean, never the field element, so value "
        ++ "agreement is not available from this routine and is not claimed"),
  routine "bnf_lt_p" .proven (some "bnfLtP_spec")
      (notes := "whole-routine triple at `GuestAddrs.bnf_lt_p`: the BN254 twin of "
        ++ "`blsgLtP_spec` over 32 bytes and `bn254PBytes`. Same ABI-only hyps"),
  routine "bnf_lt_p" .proven (some "bnfLtP_spec_specref")
      (notes := "model-facing restatement: `a0 = 1` iff `bytesBEtoNat xs < "
        ++ "SpecRef.Bn128.fieldModulus`. ⭐ NO wire-pad gate, unlike the BLS twin — "
        ++ "`Bn128.bytes_to_g1` slices `data.take 32` directly, so the guest and the "
        ++ "reference read the same 32 bytes and the restatement is total. ⚠️ It is "
        ++ "the `x`-BOUND CLAUSE of `bytes_to_g1`, not its verdict: that function "
        ++ "also bounds `y` and tests the curve equation, neither of which this "
        ++ "routine looks at"),

  -- #11925 last-of-six: `tx_type_dispatch` re-derived as `.proven` FROM THE
  -- MERGED text of #11929 (not the pre-merge read). #11929 appended the
  -- legacy upper-bound guard (0xff guard; routine 45 -> 48 instructions):
  -- `0xff` moved OUT of the legacy arm into its own FAILURE disjunct. The
  -- post remains TOTAL over the byte: empty, byte at or above 0xc0 and not
  -- 0xff -> legacy; byte equals 0xff -> ff-fail; byte under 0xc0 in 1..4 ->
  -- typed; otherwise -> unknown-fail. A failure disjunct inside a total post
  -- is still a total post. No input-domain precondition on `txBytes` (only
  -- ABI: ra-alignment, 8-aligned base, size bound, byte-access validity).
  routine "tx_type_dispatch" .proven (some "txTypeDispatch_spec_within")
      (notes := "whole-routine triple at `GuestAddrs.tx_type_dispatch` over "
        ++ "the emitted `txTypeDispatch_prog` (48 instrs after #11929's appended "
        ++ "0xff guard). Classifies via `teerTxTypeDispatch`: empty -> fail "
        ++ "(1,0,0); 0xc0..0xfe -> legacy (0,0,0); 0xff -> fail (1,0,0); 1..4 -> "
        ++ "typed (0,N,1); otherwise -> fail (1,0,0). Step budget "
        ++ "`nTxTypeDispatchSteps` = 256; five BGEU witnesses (shared, four "
        ++ "non-taken Typed, unknown) all carry immediate 168 = "
        ++ "`brOff (GuestAddrs.tx_type_dispatch+180) (GuestAddrs.tx_type_dispatch+12)`, "
        ++ "matching the emitted guard target at D+180"),
  -- #11800 follow-on: whole-routine wrapper over #11960 loop framing.
  -- Outer absorb uses signedCountdownLoop_reload_spec (hdr=LI at 0x8000368c);
  -- BLT-header signedCountdownLoop_spec does NOT apply (JAL→LI ≠ BLT 0x80003690).
  -- N/rem is length partition (len=136*N+rem, rem≤135), not an input-domain gate.
  -- Post operational keccakBodyDigest; pure SpecRef bridge absorbed by #12037
  -- (`keccakBodyDigest_eq_specref` / `_div_eq_specref`). Load-bearing consumer #12038.
  routine "zkvm_keccak256" .proven (some "zkvm_keccak256_spec_within")
      (notes := "whole-routine no-ra frame triple at GuestAddrs.zkvm_keccak256 "
        ++ "over zkvmKeccak256_prog (69 insn). Frame saves x8/x9/x18/x20 only "
        ++ "(not ra); JALR x0,x1 ret. Outer absorb loop: LI-header reload "
        ++ "(signedCountdownLoop_reload_spec) because body CSRS clobbers lim x29; "
        ++ "BLT-hdr lemma unapplied (JAL target LI 0x8000368c ≠ BLT 0x80003690). "
        ++ "Post: a0=0, output=keccakBodyDigest; pure SpecRef.keccak256 via "
        ++ "keccakBodyDigest_eq_specref (#12037). Resource/ABI only → .proven"),
  -- #12018: whole-routine SHA-256 leaf at GuestAddrs.zkvm_sha256.
  -- `sha256Cr = CodeReq.ofProg B sha256ProgL` (single-program pairing at the
  -- guest address — tier A). N/rem is the length partition
  -- (`len = 64*N+rem`, `rem < 64`), not an input-domain gate; BOTH pad arms
  -- (`rem < 56` and `rem ≥ 56`) are inside the claim. Exported post is
  -- `bytesRegion outputBase (SpecRef.sha256 input)` via the named opaque-LHS
  -- bridge `sha256BodyDigest_eq_specref`. Discharge owner for the `h_sha`
  -- residual on `erh_hash_one` (#12011).
  routine "zkvm_sha256" .proven (some "zkvm_sha256_spec_within")
      (notes := "whole-routine no-ra frame triple at GuestAddrs.zkvm_sha256 "
        ++ "over zkvmSha256_prog (121 insn). Frame saves "
        ++ "x8/x9/x18/x19/x20/x21 only (not ra); JALR x0,x1 ret. Step bound "
        ++ "`7 + sha256BodyFuel N rem + 8`. Post: output = SpecRef.sha256 via "
        ++ "sha256BodyDigest_eq_specref (opaque operational LHS; both pad arms). "
        ++ "`sha256Cr = CodeReq.ofProg` at the guest address — leaf, no "
        ++ "caller-union. Resource/ABI + accelerator hsem framing → .proven"),
  -- #12223: six-instruction ABI wrapper over the rowed `zkvm_keccak256` callee.
  -- Two claims live here now: the sponge-model triple, and (#12223 close-out)
  -- the same triple with its digest cell read against `SpecRef.headerHash`.
  routine "block_hash_from_header" .proven
      (some "block_hash_from_header_spec_within")
      (notes := "whole-routine wrapper at GuestAddrs.block_hash_from_header: "
        ++ "saves the caller return address, invokes `zkvm_keccak256` in its "
        ++ "callee frame, and restores/returns with the 32-byte digest post. "
        ++ "The composed step bound is the six-instruction wrapper plus the "
        ++ "callee's `5 + keccakBodyFuel N rem + 6` budget; resource/ABI "
        ++ "preconditions only. ⭐ SPEC-FACING COMPANION (#12223): "
        ++ "`block_hash_from_header_headerHash_within` restates that post with "
        ++ "the output cell reading `SpecRef.headerHash hdr` instead of the "
        ++ "guest's `keccakBodyDigest`. It composes the HASH leg "
        ++ "(`keccakBodyDigest_encode_eq_headerHash`, #12644) with the "
        ++ "CANONICALITY leg (`SpecRef.encode_headerToRlpItem_of_decode`, "
        ++ "#12647) through the seam lemma "
        ++ "`keccakBodyDigest_eq_headerHash_of_decode`. ⚠️ DOMAIN: everything "
        ++ "except the decode is the same resource/ABI bundle; the ONE added "
        ++ "hypothesis is `SpecRef._decode_header hb = .ok hdr`, an "
        ++ "input-domain restriction saying the supplied bytes are an "
        ++ "accepted header. The guest never CONSTRUCTS header RLP -- it "
        ++ "hashes witness bytes -- so that hypothesis is discharged from the "
        ++ "decode, not from a re-encode proof. ⚠️ NOT CLAIMED: that the "
        ++ "guest's own `header_extended_decode` agrees with "
        ++ "`SpecRef._decode_header` on those bytes (a separate correspondence "
        ++ "obligation on that routine), nor the surrounding search "
        ++ "(`blockhash_from_witness_headers` is .conditional, empty-section "
        ++ "arm). Non-vacuity: `hdec` is satisfied by the header whose hash is "
        ++ "pinned to Python at 0xaa1274..89e2, and the negative control is a "
        ++ "non-canonical re-encoding of the same header that `decodeFully` "
        ++ "accepts, `_decode_header` rejects, and whose digest differs"),
  -- #12318 callee-composition lane. `block_access_list_hash_core` is the SAME
  -- six instructions as `block_hash_from_header` above, modulo the `jalOff`
  -- displacement — which is exactly why it needs its own theorem rather than an
  -- instantiation of that one: the displacement is baked into the `Program`
  -- literal, so the two `CodeReq.ofProg`s are over DIFFERENT instruction lists.
  -- A single base-parameterised theorem would be a claim about a model; this is
  -- the claim about the linked routine at 0x8000ca78.
  --
  -- ⚠️ The `CodeReq` is a UNION of two `guestImageEntries` pairings
  -- (`blockAccessListHashCore_prog` at `GuestAddrs.block_access_list_hash_core`
  -- ∪ `zkvmKeccak256_prog` at `GuestAddrs.zkvm_keccak256`), not a single
  -- program. That is the honest requirement — the routine's `jal` really does
  -- execute the keccak image — and both halves are image pairings, so the union
  -- is still an image claim and not a model one.
  routine "block_access_list_hash_core" .proven
      (some "block_access_list_hash_core_spec_within")
      (notes := "whole-routine `cpsTripleWithin (6 + (5 + keccakBodyFuel N rem "
        ++ "+ 6))` at `GuestAddrs.block_access_list_hash_core` over "
        ++ "`wrapperCode.union keccakCode`: saves the caller return address at "
        ++ "`sp - 16`, invokes `zkvm_keccak256` in its own callee frame carved "
        ++ "from `stackFree`, restores `ra`/`sp` and returns with the 32-byte "
        ++ "`keccakCallerPost` digest. Composed from the rowed "
        ++ "`zkvm_keccak256_spec_within` via `abiFrameCall_spec` + "
        ++ "`abiFrame_spec_own`; the callee's contract is USED, not assumed. "
        ++ "The hypothesis bundle is the keccak resource bundle verbatim "
        ++ "(zk3_state alignment/validity, the `len = 136*N + rem` partition, "
        ++ "`rem ≤ 135`) — resource/ABI only, no input-domain gate → `.proven`. "
        ++ "Non-vacuity is a matched pair rather than a single instance: "
        ++ "`blockAccessListHashCore_precondition_reachable` satisfies the "
        ++ "input-dependent conjuncts on a nonempty 4-byte payload, and TWO "
        ++ "negative controls (`…_precondition_negative_control`, "
        ++ "`…_validity_negative_control`) exhibit instantiations where the "
        ++ "same conjuncts are provably FALSE. ⚠️ SCOPE: this grades the "
        ++ "wrapper's ABI and the digest of WHATEVER bytes the caller supplies; "
        ++ "that those bytes are the serialised block access list is the "
        ++ "`bal_serializer_*` rung, not this one"),
  -- #12224. The sender-authentication leg: the second keccak-calling wrapper,
  -- and the first whose post is stated against `SpecRef` rather than the guest's
  -- own sponge model.
  routine "address_from_pubkey" .proven
      (some "addressFromPubkey_spec_within")
      (notes := "whole-routine ABI-framed wrapper at "
        ++ "GuestAddrs.address_from_pubkey over "
        ++ "`(CodeReq.ofProg base addressFromPubkey_prog).union` the keccak "
        ++ "image: hashes the 64-byte public key at a0 (N = 0, rem = 64) into "
        ++ "`afp_digest`, then copies digest bytes 12-31 to the 20-byte buffer "
        ++ "at a1. Post is `SpecRef.keccak256 input |>.drop 12`, i.e. the "
        ++ "address-derivation formula against the reference, NOT the guest "
        ++ "sponge. ⚠️ GRADES THE FORMULA ONLY -- whether a0 holds the right "
        ++ "public key is the secp256k1 recover rung, a separate obligation. "
        ++ "⚠️ DOMAIN: the keccak contract fixes its output buffer to 32 zero "
        ++ "bytes and this routine never zeroes `afp_digest`; the data section "
        ++ "declares `afp_digest: .zero 32`, so the FIRST call satisfies it and "
        ++ "a second would not"),
  -- #12313. The first startable whole-routine result for the witness-header
  -- block-hash path. The empty section is an input-domain gate: it takes the
  -- early miss branch, so the nonempty scan and both already-proven callees
  -- remain outside this first tranche.
  routine "blockhash_from_witness_headers" .conditional
      (some "blockhash_from_witness_headers_spec_within_empty_section")
      (gate := "`sectionPtr = 0` — the empty witness-header section takes the "
        ++ "early miss branch before the nonempty scan. The remaining domain "
        ++ "contains the header-number extractor and keccak callees; both are "
        ++ "already `.proven`, but the scan composition is not claimed here")
      (notes := "whole-routine `cpsTripleWithin 29` at the real linked base "
        ++ "`GuestAddrs.blockhash_from_witness_headers`, over the emitted "
        ++ "77-instruction program. The proof covers the six ABI moves, the "
        ++ "empty-section BEQ, and the miss result `a0 = 1`; it does not reach "
        ++ "the nonempty scan or either external callee. The frame is saved at "
        ++ "`sp - 80`, and the spec uses concrete frame ownership at the final "
        ++ "post. The gate is an input-domain restriction, not an ABI/resource "
        ++ "hypothesis"),
  -- #12313. One-arm result for the first nonempty-loop field-7 composition.
  -- The zero-status continuation and later difficulty/nonce/ommers checks are
  -- deliberately unclaimed until their own compositions are proved.
  -- #12108. `zkvm_keccak256_segments` (70 insn) at
  -- `GuestAddrs.zkvm_keccak256_segments`, over the emitted program itself
  -- (`kssCr = CodeReq.ofProg KssB kssProgL`). This is the SCATTER-GATHER
  -- entry point `tx_signing_hash` -- and hence #12113's EIP-7702
  -- authorization digest -- hashes through, which is exactly why the landed
  -- `zkvm_keccak256_spec_within` does not reach that lane: there is no
  -- `keccakBodyDigest` to rewrite two frames down inside an unproven callee.
  --
  -- Graded `.proven`: the mid-stream rate-block permute at `KssB+148..160`
  -- (`csrs 0x800`; `s4 := 0`) is covered by the multi-rate model
  -- (`kssAbsorbed` / `kssFill` / `kssInnerLoop_spec_multi`). The routine is a
  -- LEAF: its only non-local instruction is `csrs 0x800`, an in-place 200-byte
  -- memory effect, not a control transfer, so `kssCr` constrains every address
  -- the routine executes and this row carries no unproven-callee dependency.
  -- Resource/ABI preconditions only (no INPUT-DOMAIN length gate).
  routine "zkvm_keccak256_segments" .proven
      (some "zkvm_keccak256_segments_spec_within")
      (notes := "whole-routine `cpsTripleWithin` at "
        ++ "`GuestAddrs.zkvm_keccak256_segments` from the linked entry to the "
        ++ "caller's return address, step bound `19 + kssBodyFuelMulti segs` "
        ++ "(prologue/epilogue ;; setup+zeroing 128 ;; `kssOuterFuelMulti segs` ;; "
        ++ "tail 20). `kssProg_eq_abiFrame` (`decide`) pins the routine to "
        ++ "`abiFrameProg (-64) 64 kssFrame kssBody`, so the 8-slot "
        ++ "save/restore (ra + s0-s6), callee-saved preservation and the `sp` "
        ++ "round trip are DERIVED via `abiFrame_spec_own`, not assumed. Both "
        ++ "loops are top-tested `beq ctr, zero` headers: the INNER byte loop "
        ++ "is `countdownLoop_spec` on `s6` with `bodyStep := 14` (rate path; "
        ++ "non-rate mono from 10), the OUTER segment loop is direct "
        ++ "induction on the descriptor LIST via `kssOuterLoop_spec_multi`. "
        ++ "⭐ The keccak leg is a REDUCTION: the sponge at the pad label is "
        ++ "`kssAbsorbed msg |msg|` (= `keccakBodyPrePad`), so the tail's "
        ++ "output is `keccakBodyDigest msg N rem`, and #12104's UNCONDITIONAL "
        ++ "`keccakBodyDigest_eq_specref` rewrites the post into "
        ++ "`SpecRef.keccak256 (kssMsg segs)` (`kssDigest_eq_specref_any`). "
        ++ "FOOTPRINT: the post names every cell the routine writes -- `a0`, "
        ++ "the 32-byte output buffer, and the shared 200-byte `zk3_state` "
        ++ "arena. ORDER is load-bearing and pinned: the post is "
        ++ "`SpecRef.keccak256 (segs.flatMap (·.2))` in DESCRIPTOR order. "
        ++ "Non-vacuity: `kss_sample_witness_multi` (same 3-segment gather). "
        ++ "`tx_signing_hash_spec_within` (short-domain) now exists as a "
        ++ "separate row; this row closes the segments leg of #12113's "
        ++ "`h_tsh` residual until the EIP-7702 wrapper re-points to the "
        ++ "ungated multi-rate claim. Short-domain theorems "
        ++ "(`…_within_short`, `kssOuterLoop_spec`) remain as special cases"),

  -- #11578 rescope: derive_withdrawal/consolidation_requests are NOT leaves
  -- (7-insn JAL x0 stage_system_call). Validation prefix of
  -- execution_requests_hash instead → hash-entry B+300. Hash half residual.
  -- FULL named gates (binder list, not intent): h_align listBase%8=0 (ABI a0,
  -- not static GuestAddrs pin); h_fit 20≤bs.length; h_ge ¬ult endW 20;
  -- erhOffsetsMonoW; erhGatesOkW. h_valid/h_over = ordinary memory framing.
  -- #12351: `chain_validate_post_merge_full` retired from the guest image
  -- (uncalled) and drained from this registry; Program text + offline proofs
  -- remain under ChainValidateOfflineAddrs.
  routine "execution_requests_hash" .conditional
      (some "execution_requests_hash_validation_accept")
      (notes := "validation-accept prefix at GuestAddrs.execution_requests_hash "
        ++ "(B → B+300, fuel 135): prologue sp-96 + five bgv_u32le offset reads "
        ++ "+ mono + five REMU/DIVU/cap gates. GATES (all caller hyps on the top "
        ++ "triple): h_align listBase.toNat%8=0; h_fit 20≤bs.length; h_ge "
        ++ "¬ult endW 20; erhOffsetsMonoW; erhGatesOkW. h_valid/h_over framing "
        ++ "only. coverRef erh_validation_precondition_reachable (non-empty "
        ++ "deposit 192). Hash half residual. Parked: block_state_root is "
        ++ "still String asm (`blockStateRootFunction`, "
        ++ "Codegen/Programs/BlockVerdictStateRoot.lean:297 — no `_prog`, no "
        ++ "GuestAddrs entry, no GuestImageEntries pairing). ⚠️ The former "
        ++ "\"+ requests_hash_verify\" half of this note was STALE and is "
        ++ "removed: that routine has been Program-valued since "
        ++ "`requestsHashVerify_prog` "
        ++ "(Codegen/Programs/AssembleExecutionRequests.lean:167) with the "
        ++ "String-identity theorem `requestsHashVerifyFunction_eq_prog`, and "
        ++ "as of #12206 item 2 it carries its own whole-routine row below. "
        ++ "This row's own prefix triple is what makes THAT row conditional: "
        ++ "B → B+300 does not return, so `requests_hash_verify` cannot "
        ++ "compose it and states the call under `ErhCallShape` instead"),

  -- #12206: `assemble_execution_requests` — the ONE routine of that issue with
  -- zero callees, so it proves standalone with no unproven-callee residual to
  -- state it under. Five textually identical byte-copy loops (BEQ tops at
  -- program indices 16/25/34/47/60) are ONE lemma (`aer_copy_loop`) applied
  -- five times, not five proofs.
  routine "assemble_execution_requests" .conditional
      (some "assemble_execution_requests_spec_within")
      (gate := "`aerGateOk` (a real binder of the theorem, not prose) plus the "
        ++ "SEPARATION in the precondition. Excluded inputs: (1) an output "
        ++ "buffer overlapping any of the five body buffers — the pre holds "
        ++ "`bytesRegion out ob` and the five `bytesRegion` bodies as SEPARATE "
        ++ "conjuncts and the copy loops do no overlap handling, so this is a "
        ++ "genuine domain restriction, not a framing formality; (2) an output "
        ++ "buffer shorter than `20 + Σ body lengths`; (3) an output pointer or "
        ++ "body pointer that is not 8-aligned; (4) length registers `a1`/`a3`/"
        ++ "`a5` or the `aer_bd_len`/`aer_be_len` globals disagreeing with the "
        ++ "modelled body lengths (`hdl`…`hbel`). Alignment / `isValid*Access` / "
        ++ "no-wrap are ordinary resource framing. Non-vacuity: "
        ++ "`aer_gate_reachable` (bodies 4/2/0/1/3 bytes at 8-aligned RAM "
        ++ "addresses — note the 0 makes one of the five loops run zero "
        ++ "iterations) with TWO negative controls, `aer_gate_not_8aligned` and "
        ++ "`aer_gate_buffer_too_short`, where the gate is provably FALSE")
      (notes := "`cpsTripleWithin (aerFuel (ntot - 20))` — 50 straight-line "
        ++ "steps plus 7 per copied body byte — at "
        ++ "`GuestAddrs.assemble_execution_requests` over `aerCode = "
        ++ "CodeReq.ofProg B assembleExecutionRequests_prog`, exit "
        ++ "`ra &&& ~~~1`. NO callee union: the routine calls nothing, which is "
        ++ "why #12206's other two residuals (`requests_hash_verify`, "
        ++ "`stage_system_call`) are harder despite being smaller. Post: (a) "
        ++ "`out[0..20)` holds the five little-endian u32 EIP-7685 SSZ offsets "
        ++ "`20, 20+dl, 20+dl+wl, 20+dl+wl+cl, 20+dl+wl+cl+bdl`; (b) `out[20..)` "
        ++ "holds `deposits ‖ withdrawals ‖ consolidations ‖ builder_deposits ‖ "
        ++ "builder_exits` in that order (`aerSection`, a nest of `setBytes`); "
        ++ "(c) `a0 = 20 + dl + wl + cl + bdl + bel`. Header `SW`s and body "
        ++ "`SB`s write the SAME `bytesRegion out …`, so the header/body "
        ++ "aliasing at `out[16..24)` is discharged by `setBytes` index "
        ++ "arithmetic rather than assumed away. Split across "
        ++ "`AssembleExecutionRequests{Base,Copy,Header,Body,Tail,Top}`"),

  -- #12206 item 2: `requests_hash_verify` whole-routine triple. 36 instructions
  -- at 0x8005434c (144 bytes, ret at 0x800543d8), ONE loop (the 32-byte compare
  -- at 0x80054394) and TWO callees. `assemble_execution_requests` is COMPOSED
  -- from the row above; `execution_requests_hash` cannot be — its row covers a
  -- non-returning validation prefix — so that call stands under a named
  -- residual. Three exit codes, all in the post.
  routine "requests_hash_verify" .conditional
      (some "requests_hash_verify_spec_within")
      (gate := "ONE input-domain binder plus ONE forwarded one, and TWO "
        ++ "residuals that are DEPENDENCIES, not gates. INPUT DOMAIN: (1) "
        ++ "`rhvGateOk expPtr dig exp` — about the CALLER's expected-hash "
        ++ "buffer ONLY: `dig.length = 32`, `exp.length = 32`, "
        ++ "`expPtr.toNat % 8 = 0`, `expPtr.toNat + 32 < 2^64`, and "
        ++ "`isValidByteAccess` for all 32 bytes. The `rhv_hash` side "
        ++ "(`GuestAddrs.rhv_hash`) is PROVED, not assumed — `rhvHash_gate` "
        ++ "decides "
        ++ "alignment, no-wrap and all 32 byte-validity facts. (2) `aerGateOk` "
        ++ "— forwarded verbatim to the composed callee; see the "
        ++ "`assemble_execution_requests` row for what it excludes. `halign` "
        ++ "(even return address) is the ordinary ABI obligation; the "
        ++ "`bytesRegion` SEPARATION between the section buffer, the five "
        ++ "bodies, `rhv_hash` and the expected-hash buffer is a real domain "
        ++ "restriction (the routine does no overlap handling). RESIDUAL: "
        ++ "`h_erh : ErhCallShape` at index 12 (0x8005437c) — an "
        ++ "UNPROVEN-CALLEE DEPENDENCY on `execution_requests_hash`, whose own "
        ++ "row covers only the validation-accept prefix `B → B+300` and "
        ++ "therefore never returns to this caller. The residual leaves the "
        ++ "digest ABSTRACT on purpose, so the triple proves this routine's "
        ++ "whole behaviour (compare 32 bytes, report 0/1/2) against ANY "
        ++ "digest; what it does not say is `dig = requests_hash(section)`, "
        ++ "which is the inherited `Hash half residual` with owner #12018 "
        ++ "(`zkvm_sha256_spec_within` via `shaCallWithinShape`), then the "
        ++ "return path of `execution_requests_hash` itself. Non-vacuity: "
        ++ "`rhv_gate_reachable` and `rhv_residual_reachable` (the residual's "
        ++ "computable conjuncts discharged at the REAL call site by "
        ++ "`erhCallSite_ok`), with THREE negative controls where the same "
        ++ "bundles are provably FALSE — `rhv_gate_unaligned`, "
        ++ "`rhv_gate_short_expected`, `rhv_residual_wrong_site` (the same "
        ++ "shape at index 7, where the `jal` targets the other callee). "
        ++ "`rhv_verdict_match/mismatch/hashfail_reachable` additionally show "
        ++ "the post is NOT constant across the three codes")
      (notes := "`cpsTripleWithin (rhvFuel (ntot - 20) erhFuel)` at "
        ++ "`GuestAddrs.requests_hash_verify` (0x8005434c) with exit `ret`, "
        ++ "over `rhvCode = CodeReq.ofProg B requestsHashVerify_prog ∪ "
        ++ "aerCode` — the callee union is REAL: the composed call steps "
        ++ "through `assemble_execution_requests`'s own text. Prologue and "
        ++ "epilogue come from `abiFrame_spec` over the kernel-checked "
        ++ "decomposition `rhvProg_eq_abiFrame` (`rhvProgL = abiFrameProg "
        ++ "(-32) 32 rhvFrame rhvBody`, frame `[(x1,0),(x8,8),(x9,16)]`), so "
        ++ "only indices 4–31 are proved by hand. THREE EXIT CODES, all in the "
        ++ "post via `rhvVerdict st dig exp`: `a0 = 2` when the callee "
        ++ "reported failure (`bnez a0` at 0x80054380 taken → `li a0, 2` at "
        ++ "0x800543c4, `rhv_status_branch_fail` + `rhv_hashfail_verdict`); "
        ++ "`a0 = 1` on a byte mismatch (`bne t3,t4` at 0x800543a0 taken → "
        ++ "`li a0, 1` at 0x800543bc); `a0 = 0` on a full match (`beqz t2` at "
        ++ "0x80054394 taken → `li a0, 0` at 0x800543b4) — the last two from "
        ++ "`rhv_cmp_tail`, one triple covering BOTH loop exits by downward "
        ++ "induction with a per-byte case split. FOOTPRINT: the post names "
        ++ "every cell the routine writes — `a0`, the scratch section buffer "
        ++ "(now the assembled SSZ section), the 32 `rhv_hash` BSS bytes the "
        ++ "callee filled, and the restored `ra`/`s0`/`s1`; every caller-saved "
        ++ "register either callee may clobber is OWNED in the post, not "
        ++ "pinned. ⚠️ `erhScratchOwn` deliberately puts x5-x7/x13-x17/x28-x31 "
        ++ "in the residual's FOOTPRINT rather than its frame: "
        ++ "`cpsTripleWithin` quantifies over all frames, so a register the "
        ++ "footprint omits could be instantiated as pinned by a caller and "
        ++ "the shape would be undischargeable for any real callee. ⚠️ No "
        ++ "Correspondence row: the digest is abstract under the residual, so "
        ++ "this triple ties to no spec-side VALUE and a correspondence "
        ++ "verdict would overstate it"),

  -- #12038: K145 `tx_signing_hash` whole-routine triple, multi-rate segments.
  -- Long8 wired through Prefix/PrefixGate/Join/Spec — no residual
  -- `payloadLen < 2^56` gate. Keccak gather ungated via
  -- `zkvm_keccak256_segments_spec_within` (`kssCallerPost_multi` /
  -- `kssBodyFuelMulti`). Prefix BSS ownership is 16 zero-init bytes; gather
  -- hashes bare `rlpListPrefix` (NH ≤ 9); trailing dword when NH ≤ 8 is
  -- `tshPrefixBssTail` (zero BSS unused by any segs descriptor).
  routine "tx_signing_hash" .conditional
      (some "tx_signing_hash_spec_within")
      (gate := "any outer-RLP LIST header: 0xc0 ≤ input[0] ≤ 0xff, the " ++
        "theorem's remaining hge domain. Short (0xc0–0xf7) AND long " ++
        "(0xf8–0xff, lenlen 1..8) are BOTH covered, by one theorem: the " ++
        "parsed header length is threaded as `tshHdrLen` (= 1 short, " ++
        "hdr-246 long) instead of case-split. REMAINING CUT: non-list first " ++
        "bytes 0x00–0xbf, where the guest takes its status-1 reject path and " ++
        "exits at tshFailLiPC rather than through this triple.")
      (notes := "whole-routine `cpsTripleWithin` at `GuestAddrs.tx_signing_hash` "
        ++ "via `abiFrame_spec_own` over the emitted frame (H pin = "
        ++ "`BitVec.ofNat 64 GuestAddrs.tx_signing_hash` in TxSigningHashSpecCore). "
        ++ "Preconditions static (buffers, alignment, header-shape, index/list "
        ++ "lengths); nth ok vs fail live in the post disjunction "
        ++ "`tshTypedSuccessCallerPost`. Body split across "
        ++ "TxSigningHashSpec{Core,BodyEarly,BodyLate,Success,Prefix,PrefixGate,Join}. "
        ++ "Prefix BSS zero-init 16 bytes; `segs` use bare `rlpListPrefix`; "
        ++ "`tsh_prefix_any_callWithin` total on `Word` (short+long1..long8). "
        ++ "ABI for prefix (`out%8=0`, `|out|>8`, validity) discharged at the "
        ++ "call site. Multi-rate segments post (`kssAbsorbed`/`kssFill`). "
        ++ "LONG OUTER HEADER: `tshHdrParseAny_spec` (H+72→H+108, 8 steps) "
        ++ "covers both arms of the `bltu t0,248`; the long arm's two `addi`s "
        ++ "give `s5 = hdr-246 = 1+lenlen`, and that value is threaded as the "
        ++ "`hdrLen` parameter through Success/Join/Spec and the KSS payload "
        ++ "source (`kssInputSource` now at `base + hdrLen`). NON-VACUITY: "
        ++ "`tsh_longHdr_domain_nonvacuous` (f8 42 outer header, the type-2 / "
        ++ "32-byte-calldata shape, hdrLen = 2, with a matching "
        ++ "`RlpListNthItemSAsm.Success` + `tshPayloadLenEq`); negative "
        ++ "controls `tsh_hdrGate_false_on_string_header` (hge FALSE at 0x80) "
        ++ "and `tsh_longArm_gate_false_on_short_header` (long-arm gate FALSE "
        ++ "at 0xc4). "
        ++ "Empty-len fail (`a1 = 0`) is a SEPARATE slice "
        ++ "(`tx_signing_hash_spec_within_empty_len`), not a second registry "
        ++ "row. ⚠️ Does NOT claim SpecRef `signing_hash_*`"),

  -- #12038: K147 EIP-7702 authorization-signing-hash wrapper. Owns n=3,
  -- MAGIC=0x05, a2→a4 output forward; delegates the rest to K145 by one
  -- cross-`jal`.
  --
  -- ⚠️ There is NO input-domain gate on this row. `auth` ranges over every
  -- `Authorization`; `sp0`/`inPtr`/`outPtr`/`lenW` over every word. The
  -- condition is still an UNPROVEN-CALLEE DEPENDENCY (`txSigningHashContract`)
  -- until the wrapper is re-pointed onto `tx_signing_hash_spec_within`
  -- (short-domain triple now exists as its own row). A `.proven` row would
  -- overclaim while `h_tsh` remains a hypothesis, so the tier stays
  -- `.conditional` and the gate field names the residual.
  --
  -- ⚠️ NOT tied to `SpecRef.Transactions.signing_hash_*`: the EIP-7702
  -- *authorization* digest is not one of those six (they are the TRANSACTION
  -- signing hashes). It lives inline in `SpecRef.Interpreter.recover_authority`
  -- keyed on `SET_CODE_TX_MAGIC`, and `recover_authority_unfold` (by `rfl`) is
  -- the tie.
  routine "eip7702_authorization_signing_hash" .conditional
      (some "eip7702_authorization_signing_hash_spec_within")
      (gate := "NOT an input-domain gate — an UNPROVEN-CALLEE DEPENDENCY. The "
        ++ "one condition is `h_tsh : txSigningHashContract`, the whole-routine "
        ++ "calling contract of K145 `tx_signing_hash` at the site "
        ++ "eip7702_authorization_signing_hash+20. The short-domain machine "
        ++ "triple `tx_signing_hash_spec_within` now EXISTS (own registry row); "
        ++ "what remains open is discharging this residual / re-pointing the "
        ++ "wrapper onto that triple. The residual is stated GENERIC in "
        ++ "(n_fields, type_prefix) — a `∀ nW prefixW, nW.toNat ≤ fields.length` "
        ++ "family — so the wrapper's 3 and 0x05 are DERIVED from the machine's "
        ++ "two LIs, not assumed; the `≤ fields.length` bound is load-bearing "
        ++ "(beyond it the callee returns status 1 and writes no hash, so an "
        ++ "unbounded ∀ would be a FALSE hypothesis). Every non-triple conjunct "
        ++ "of the residual is discharged at the real call site: coverRef "
        ++ "`authCallSite_ok_sample`, a closed term on the concrete "
        ++ "`sampleAuth` (chain id 1, delegate 0xDD*20, nonce 0) with its "
        ++ "27-byte tuple and a zeroed 32-byte output buffer. The remaining "
        ++ "hypotheses are ABI/framing obligations, not domain restrictions: "
        ++ "`halign` (even return address, witnessed by `sample_ret_align`) "
        ++ "and `hF` (caller-frame pcFree)")
      (notes := "whole-routine triple at GuestAddrs.eip7702_authorization_signing_hash "
        ++ "over eip7702AuthorizationSigningHash_prog (9 insn) via abiFrame_spec; "
        ++ "frame = [(x1,0)] at sp-16, step budget `authSteps fuel` = "
        ++ "1+1+(3+(1+fuel))+1+1+1. Structural drift guard "
        ++ "`eip7702AuthorizationSigningHash_prog_eq_frame` (rfl) pins the "
        ++ "emitted routine to abiFrameProg(-16,16,[(x1,0)],authBody); "
        ++ "`authJal_target` (decide) pins the cross-jal reloc to "
        ++ "GuestAddrs.tx_signing_hash. Post: a0=0, tuple region intact, output "
        ++ "region = `authSigningHash auth`, which `recover_authority_unfold` "
        ++ "(rfl) shows IS the digest SpecRef.recover_authority feeds to "
        ++ "Secp256k1.recover — a reduction, not a transcription. Field-position "
        ++ "pinning: `authSigningPreimage_segments` (general, short-list form) "
        ++ "and `sampleAuth_preimage` (concrete 25 bytes: MAGIC[0], list "
        ++ "header[1], chain_id[2], 0x94+address[3..23], nonce[24]) — not "
        ++ "symmetric in any two fields. Six-field wire layout confirmed against "
        ++ "SpecRef's PUBLIC decoder by `sampleAuth_decodes`. Segments leg "
        ++ "(`zkvm_keccak256_segments`) and short-domain K145 "
        ++ "(`tx_signing_hash_spec_within`) are both rowed; residual "
        ++ "retirement is wrapper re-point onto that triple. Retirement: "
        ++ "`txSigningHashResidualNote`"),
  -- #11800, the node-DB half. Whole-routine triple over the emitted
  -- `nodeDbLookup_prog` (33 insn) at `GuestAddrs.node_db_lookup`; the machine
  -- appears in the statement (`ndlCr = CodeReq.ofProg ndlB nodeDbLookup_prog`),
  -- not just a model of it. Graded `.proven`, not `.conditional`: there is NO
  -- input-domain gate and NO unproven-callee dependency. `node_db_lookup` is a
  -- leaf -- it calls nothing, and in particular it does NOT hash: it compares
  -- the digest ALREADY STORED in each record against the caller's target, so
  -- the keccak obligation that `node_db_append` carries simply does not arise
  -- here. Every hypothesis is resource/ABI: `hsh.length = 32` (the a0 buffer
  -- the four-dword cascade reads), `(keccak256 m).length = 32` for the stored
  -- digests -- which is `Stateless.SpecRef.keccak256_length`, unconditionally
  -- true, so it excludes nothing -- u64-representability of node lengths and
  -- of the record count, and two-byte return-address alignment. The post is
  -- TOTAL: both the hit and the miss arm are inside the claim.
  routine "node_db_lookup" .proven (some "node_db_lookup_spec_within")
      (notes := "whole-routine `cpsTripleWithin` at `GuestAddrs.node_db_lookup`, "
        ++ "step bound `5 + 20 * |nodes| + 3` (prologue ;; per-record round ;; "
        ++ "exhaustion tail). Post is a `match` on `nodeDbFind`, the "
        ++ "address-carrying refinement of `MptAssertions.nodeDbLookupSpec`: a "
        ++ "hit pins `a0 = 0`, `*a1 = cursor + 40` (the record's NODE-BYTES "
        ++ "address) and `*a2 = |node|` -- two different cells holding two "
        ++ "different quantities, so the claim would not survive swapping them; "
        ++ "a miss pins `a0 = 1` and both cells UNCHANGED, not merely owned. "
        ++ "First-match-ness is real: the loop invariant carries "
        ++ "`nodeDbLookupSpec (take j) = none`. The four-`BNE` cascade is shown "
        ++ "to decide a 32-byte comparison exactly (`eq_of_dwords_eq`), and the "
        ++ "`andi -8` cursor bump to be exactly `nodeDbStride` "
        ++ "(`roundUp8_eq_alignToDword`). Composition to the spec reference is "
        ++ "`node_db_lookup_result_eq_build_node_db`, chaining the pre-existing "
        ++ "`nodeDbLookupSpec_eq_build_node_db` -- so the published length is "
        ++ "the length of the node `witness_state.py`'s `node_db` maps the hash "
        ++ "to. Non-vacuity is a COMPILED instantiation, "
        ++ "`node_db_lookup_sample_witness`: a closed one-record DB whose post "
        ++ "is reduced to the HIT arm. ⚠️ NOT established here: that "
        ++ "`node_db_append` establishes the `nodeDbIs` shape this triple "
        ++ "consumes (that is the append half, still open), and `bytesRegion`'s "
        ++ "dword-aligned-base convention is assumed of `mset_db_data`, not "
        ++ "derived from the link map"),
  -- #12036. `witness_lookup_by_hash` (155 insn) at
  -- `GuestAddrs.witness_lookup_by_hash`, over the emitted program itself
  -- (`wlhCr = CodeReq.ofProg wlhB witnessLookupByHash_prog`). Graded
  -- `.conditional` on an INPUT-DOMAIN gate, not on a callee: the routine's two
  -- cross-`jal`s (`witness_lookup_by_hash_indexed`, `zkvm_keccak256`) are both
  -- UNREACHED on the domain claimed, so this row carries no unproven-callee
  -- dependency -- but the general routine does, and the extension past either
  -- branch must carry those contracts as hypotheses.
  routine "witness_lookup_by_hash" .conditional
      (some "witness_lookup_by_hash_spec_within_enabled_empty")
      (gate := "PRODUCTION empty-miss: `widx_enabled = 1` and `widx_count = 0` "
        ++ "(REACHABLE: empty-section build succeeds with enable=1). "
        ++ "Three walk sites (root pc35, branch pc101, ext pc210) establish "
        ++ "`wlCallWithinShapeEn` under walk fullCode via "
        ++ "`root/branch/ext_wl_enabled_empty_establishes_shape` (#12183). "
        ++ "Legacy alternate: `witness_lookup_by_hash_spec_within_empty_section` "
        ++ "under `widx_enabled = 0` (linear miss; not production walk ambient). "
        ++ "Both arms exclude the WORK: non-empty indexed binary search and the "
        ++ "linear scan loop (`+308 … +552`) with `zkvm_keccak256`. NOT a size "
        ++ "cap. Non-vacuity: compiled samples on both tops + three-site residual")
      (notes := "PRODUCTION top: whole-routine `cpsTripleWithin 87` "
        ++ "`witness_lookup_by_hash_spec_within_enabled_empty` via "
        ++ "`abiFrame_spec_own` over `enableFullCode = wlhCr ∪ indexed`. Path: "
        ++ "enable fallthrough → section match → ABI restore → idx_calls bump → "
        ++ "JAL indexed empty-miss (fuel 28) → idx_miss bump → epi. Nested Own "
        ++ "at newSp-64 (walk residual needs `stackFree sp0 16` — SAY SO). "
        ++ "Walk `fullCode` unions indexed so `enableFullCode ⊆ fullCode`. "
        ++ "Residual: `wlhCallWithin_enabled_empty` fuel 1+87 + "
        ++ "`wlCallWithinShapeEn` (same ambient; not vacuous) discharged at "
        ++ "three sites by `MptWalkWlEnabledEmpty`. LEGACY top: "
        ++ "`cpsTripleWithin 52` empty_section (enable=0 linear) + "
        ++ "`MptWalkWlEmpty` three sites. HIT top (#12036): "
        ++ "`witness_lookup_by_hash_spec_within_enabled_one_hit`, whole-routine "
        ++ "`cpsTripleWithin 402` on `widx_enabled = 1`, `widx_count = 1`, "
        ++ "section ptr/len MATCHED but both free (not zero), target hash equal "
        ++ "to the sole record's; post `a0 = 0`, out cells written "
        ++ "`(hitOffW, hitLenW)`, `lookup/indexed_calls/indexed_hits` each +1. "
        ++ "Path: setup → indexed one-hit callee (fuel 343) → BNE ntaken → "
        ++ "indexed_hits bump → JAL epi. Composable only because "
        ++ "`witness_lookup_by_hash_indexed_spec_within_one_hit_gen` leaves the "
        ++ "scratch temps symbolic: the zeros-pinned #12192 form fixed "
        ++ "`x6 = 0` while the parent arrives with "
        ++ "`x6 = wlh_indexed_calls + 1`. HIT residual (#12036): "
        ++ "`wlhCallWithin_enabled_one_hit` fuel 1+402 + "
        ++ "`wlCallWithinShapeHitEn` (same ambient; not vacuous — closed "
        ++ "instance `root_wl_enabled_hit_shape_sat`, negative control "
        ++ "`root_wl_enabled_hit_shape_wrong_offset_false`), discharged at the "
        ++ "three walk sites by `MptWalkWlEnabledHit` "
        ++ "(`root/branch/ext_wl_enabled_hit_establishes_shape`), so the hit "
        ++ "residual at those sites is a THEOREM at `widx_count = 1`, not a "
        ++ "hypothesis. STILL OPEN: arbitrary `widx_count` (the real binary "
        ++ "search) and the linear scan with `zkvm_keccak256`; and the "
        ++ "enable=0-shaped `MptWalkResidualChain.wlCallWithinShapeHit` "
        ++ "(`stackFree sp0 8`, six-cell `wlTelemetry`, no index cells) is a "
        ++ "DIFFERENT residual that stays a free `h_wl` on "
        ++ "`root/branch/ext_wl_hit_chain` — no enable=1 arm can produce that "
        ++ "shape. Non-vacuity: #12690's PARTIAL is now closed — "
        ++ "`hit_site_entryState_exists` exhibits a concrete `MachineState` "
        ++ "satisfying the residual's precondition (65 pairwise-distinct "
        ++ "register/memory atoms: 16 free stack dwords, the eleven `widx_*` / "
        ++ "`wlh_*` cells, `wlh_indexed_hits`, both 32-byte hash regions and "
        ++ "the four out/record cells), so the fuel-402 `callWithin` is not a "
        ++ "vacuously-true triple"),
  -- #12244: the byte-reversing copy, ONE proof rowed at TWO guest addresses.
  -- `bhrRevLeBe_prog` is byte-identical to `swrRevLeBe_prog` and `bhrRevLeBeFn`
  -- is a definitional alias of `swrRevLeBeFn`, so `revLeBeFlat_at` is
  -- parameterized over the base + program and instantiated twice, each pairing
  -- discharged by `rfl`. Both allowlist entries read "needs Fn.retSpecFlat
  -- before a .proven row is honest (#11637)"; that debt is paid.
  -- ⚠️ Correction worth recording: the blocker was NOT that a 3-ABI-register
  -- split had no template. `U256BeFlat.exposedRegs_split_add` splits the SAME
  -- fifteen exposed registers around the SAME three, and this lift is ported
  -- from it. The real blocker was the `Fn` post not pinning its ambient.
  routine "swr_rev_le_be" .proven (some "swrRevLeBeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.swr_rev_le_be` over "
        ++ "`CodeReq.ofProg … swrRevLeBe_prog`, 10 insn: reverses the first "
        ++ "`len` bytes of the read-only region at `a0` into the `len`-byte "
        ++ "writable window at `a2`, i.e. `[a2] = (bs.take len).reverse`. The "
        ++ "SOURCE region is pinned INTACT in the post, so a routine that "
        ++ "scribbled on its input could not satisfy this. Three ABI registers "
        ++ "pinned (`a0`=src, `a1`=len, `a2`=dst) via the three-way "
        ++ "`exposedRegs_split_rev`, ported from `U256BeFlat`'s "
        ++ "`exposedRegs_split_add`. ⚠️ NOT total over its argument types: "
        ++ "beyond lengths / region wf / no address wraparound it needs "
        ++ "src-dst DISJOINTNESS, and that is a real domain restriction rather "
        ++ "than framing convenience — the block engine's `inRw` routing test "
        ++ "is ARITHMETIC, so without it an `LBU` aimed at the source could be "
        ++ "routed into the writable window and read a PARTIALLY REVERSED "
        ++ "byte. An overlapping caller genuinely cannot satisfy the contract, "
        ++ "which matches the routine's real contract (reverse-copy into a "
        ++ "separate buffer). Lives in "
        ++ "`Codegen/Proofs/RevLeBeFlatTriples.lean`"),
  routine "bhr_rev_le_be" .proven (some "bhrRevLeBeFlat_spec")
      (notes := "whole-routine triple at `GuestAddrs.bhr_rev_le_be` over "
        ++ "`CodeReq.ofProg … bhrRevLeBe_prog`. The SAME routine as "
        ++ "`swr_rev_le_be`, deployed at a second address under a second "
        ++ "label: same contract, same 10 instructions, same source-intact "
        ++ "post and same src-dst disjointness requirement (see that row for "
        ++ "why `hdj` is load-bearing). NOT a second proof — both rows "
        ++ "instantiate the base-parameterized `revLeBeFlat_at`, and that the "
        ++ "one lemma accepts both `GuestImageEntries` pairings by `rfl` is "
        ++ "itself the byte-identity witness (the body's `flatten` is "
        ++ "base-independent). Lives in "
        ++ "`Codegen/Proofs/RevLeBeFlatTriples.lean`"),
  -- #12222: the BAL read-half producer's FIRST rowed claim. In-degree 10 with
  -- no theorem at all before this; the row covers ONE of the routine's four
  -- arms, so the gate below is what keeps it honest rather than `.proven`.
  routine "account_read_record" .conditional
      (some "accountReadRecordSuppressedFlat_spec")
      (gate := "`runtime_tx_account_read_suppress ≠ 0` — the SUPPRESSED arm "
        ++ "only (the `bne t1, zero` at instruction index 11, TAKEN). This is "
        ++ "a genuine input-domain gate, not framing: the three arms it "
        ++ "excludes are the ones the fall-through reaches at index 12 "
        ++ "(overflow when `tx_account_reads_count ≥ 0x4000`, dedup hit, and "
        ++ "append), and those run the fixed-stride scan at indices 12..63 "
        ++ "with a nested 20-byte byte-compare loop — no invariant is claimed "
        ++ "for them here. coverRef: the two `example`s at the end of "
        ++ "`Codegen/Proofs/AccountReadRecordSpec.lean` — a fully numeric "
        ++ "instance (`sp = 0x30000000`, flag `1`, temps `1..7`, the seven "
        ++ "spill slots read back numerically) plus a NEGATIVE control "
        ++ "(`¬((0 : Word) ≠ 0)`) showing the gate really excludes the "
        ++ "recording inputs")
      (notes := "`cpsTripleWithin 21` at `GuestAddrs.account_read_record` over "
        ++ "`CodeReq.ofProg … accountReadRecord_prog` — the "
        ++ "`GuestImageEntries` pairing itself, so entry AND CodeReq are both "
        ++ "at the anchor (whole-routine in the `proof-frontier.py --shape` "
        ++ "sense). Path `0..11 ;; 64..72`: prologue (`sp -= 64`, spill "
        ++ "`t0`-`t6`) ;; `la t0, runtime_tx_account_read_suppress` ;; `ld t1` "
        ++ ";; `bne` TAKEN ;; epilogue (reload the seven temps, `sp += 64`, "
        ++ "`ret`). The post is the NO-OP claim the routine's calling "
        ++ "convention advertises: `sp` restored, all seven temps back to "
        ++ "their entry values, `a0` (the 20-byte address pointer) untouched, "
        ++ "the suppression cell unchanged. Because `cpsTripleWithin` "
        ++ "quantifies over a `pcFree` frame, the post ALSO says — for free, "
        ++ "by not naming them — that this arm writes nothing to "
        ++ "`tx_account_reads_count`, `tx_account_reads_overflow` or the "
        ++ "`TX_ACCOUNT_READS_AREA` arena. That is the spec-side meaning of "
        ++ "the gate: a suppressed read cannot enter `account_reads` and so "
        ++ "cannot reach `add_touched_account` "
        ++ "(`block_access_lists.py:696`). ⚠️ No Correspondence row is added: "
        ++ "this arm ties to no spec-side VALUE, only to the absence of a "
        ++ "record, so a correspondence verdict would overstate it. Lives in "
        ++ "`Codegen/Proofs/AccountReadRecordSpec.lean`")
]

/-! ## Counts (kernel-checked) -/

/-- Rows in the guest-routine registry. -/
def routineCount : Nat := routineRegistry.length

/-- Rows at a given tier. -/
def routineCountTier (t : ProofTier) : Nat :=
  (routineRegistry.filter (fun e => e.tier == t)).length

-- ⚠️ The registry list outgrew `decide`'s default recursion budget at 126 rows
-- (#12244). These three totals are still KERNEL-CHECKED — raising `maxRecDepth`
-- only lets the elaborator finish unfolding the list; it does not weaken the
-- check, and none of the forbidden tactics is involved.
set_option maxRecDepth 16000 in
theorem routineCount_eq : routineCount = 203 := by decide

set_option maxRecDepth 16000 in
theorem routineProvenCount_eq : routineCountTier .proven = 158 := by decide
set_option maxRecDepth 16000 in
theorem routineConditionalCount_eq : routineCountTier .conditional = 42 := by decide
set_option maxRecDepth 16000 in
theorem routinePartlyCount_eq      : routineCountTier .partly      = 3 := by decide

/-- Every row names a witness theorem. The `none` case is what
    `scripts/gen-axiom-witnesses.py`'s cross-check would report as an
    unwitnessed row; asserting it here makes the registry itself refuse one. -/
theorem routineRegistry_all_witnessed :
    routineRegistry.all (fun e => e.proofRef.isSome) = true := by decide

/-- Distinct guest symbols covered. Lower than `routineCount` because a
    per-form routine contributes several rows. -/
def routineSymbols : List String :=
  routineRegistry.map (·.symbol) |>.eraseDups

-- ⚠️ `eraseDups` over 150 rows is deeper than the tier counts, so this one needs a
-- larger budget than the 8000 above. Still kernel-checked; see the note there.
set_option maxRecDepth 40000 in
theorem routineSymbols_eq : routineSymbols.length = 165 := by decide

/-! ## Cross-registry consistency (#11294)

    This registry and `Correspondence.lean` describe overlapping facts in
    different vocabularies: a row here is a *witnessed theorem* about a symbol;
    a row there is a *verdict* about the same symbol. Nothing else compares
    them — `gen-axiom-witnesses.py`'s cross-check keys on theorem names, and an
    `.unproven` Correspondence row has `spec := none`, so it contributes no
    name at all and is invisible to that check by construction.

    The theorem below closes the gap in the direction that already bit once
    (#11281: `rlp_encode_uint_be` sat `.unproven` while `reub_spec_within`
    existed): a symbol witnessed here must not read `.unproven` there. Both
    registries would now have to be wrong in the same way for a stale verdict
    to survive. `scripts/check-registry-crosscheck.sh` enforces the same
    invariant source-level so it fails in `source-checks` in seconds rather
    than an hour into the build. -/

/-- `false` iff some entry of `reg` carries verdict `.unproven` for a routine
    in `witnessed`. Factored out of the theorem so the negative control below
    can run the same decision procedure on a synthetic violation. -/
def crossVerdictOk (witnessed : List String)
    (reg : List Correspondence.Entry) : Bool :=
  reg.all fun e =>
    e.verdict != .unproven || !(witnessed.contains e.routine)

set_option maxRecDepth 40000 in
/-- A routine with a witnessed row here must not be `.unproven` in
    `Correspondence.registry`. -/
theorem witnessed_not_unproven :
    crossVerdictOk routineSymbols Correspondence.registry = true := by decide

/-- Negative control, kernel-checked on every build: `rlp_encode_u64` is a real
    `.unproven` Correspondence row today, so witnessing it here would make the
    check fire. A gate nobody has seen fail is indistinguishable from one that
    cannot. (Was `rlp_item_span` until #11577 lifted that row.) -/
example :
    crossVerdictOk ("rlp_encode_u64" :: routineSymbols) Correspondence.registry
      = false := by decide

/-! ## Witness `abbrev`s

    Each row above names a theorem; the abbrev below forces its definition to
    exist, so a rename or deletion fails this file's elaboration. These are
    also what `scripts/gen-axiom-witnesses.py` greps to emit `#print axioms`
    lines, which is how these theorems reach `scripts/check-axioms.sh`.

    ⚠️ The generator's name pattern must admit these namespaces. Before #11042
    it was `@EvmAsm\.(?:Evm64|Stateless)…`, which silently matched **nothing**
    for `@EvmAsm.Codegen.…` — so an abbrev added here without widening the
    pattern would have left the gate green while covering nothing. The
    generator now also cross-checks every `proofRef` against the extracted
    names and fails loudly on a row it cannot witness.

    Convention: name the abbrev `_<lower>_routine_witness`; mark it
    `private noncomputable` to avoid polluting the namespace. -/

private noncomputable abbrev _reub_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_spec_within
private noncomputable abbrev _reub_encode_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_spec_encode_within
private noncomputable abbrev _reub_length_le_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_spec_within_of_length_le
private noncomputable abbrev _reb_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeBytesSAsm.reb_spec_within
private noncomputable abbrev _reb_rlpItem_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeBytesSAsm.reb_spec_rlpItem_within
-- #10780 item 3: the two long-form arms, their reference-tied corollaries, and the two
-- reachability witnesses their `.conditional` rows name as coverRefs (#12014's ruling).
-- The corollaries are witnessed separately from the triples on purpose: they are where
-- the `decode`/`readLength` hypotheses enter, and a reader should be able to see which
-- claim is the machine result and which is the model identification.
-- #10780: the TOTAL dispatch — one triple over all five RLP prefix forms, no `SpanForm`
-- gate. Witnessed but deliberately NOT re-graded: `rlp_item_size` keeps its
-- `.conditional` row on `rlp_item_size_spec_within`, because the total statement carries a
-- prefix-dependent step bound and a seven-register footprint where the existing one is
-- constant-time over two, and which of those a consumer wants is a per-caller decision.
-- Additive by construction: nothing consuming `SpanForm` changes.
private noncomputable abbrev _rlp_item_size_total_witness :=
  @EvmAsm.Codegen.RlpItemSizeTotalSpec.rlp_item_size_total_spec_within
private noncomputable abbrev _rlp_item_size_total_covers_witness :=
  @EvmAsm.Codegen.RlpItemSizeTotalSpec.risStepsTotal_covers
private noncomputable abbrev _rlp_item_size_total_bound_witness :=
  @EvmAsm.Codegen.RlpItemSizeTotalSpec.risStepsTotal_le
private noncomputable abbrev _rlp_item_size_long_string_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_string_pinned_spec_within
private noncomputable abbrev _rlp_item_size_long_list_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_list_pinned_spec_within
private noncomputable abbrev _rlp_item_size_long_string_encode_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_string_encode_length_spec_within
private noncomputable abbrev _rlp_item_size_long_list_encode_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.rlp_item_size_long_list_encode_length_spec_within
private noncomputable abbrev _rlp_item_size_long_string_cover_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.longStringSample_reachable
private noncomputable abbrev _rlp_item_size_long_list_cover_witness :=
  @EvmAsm.Codegen.RlpItemSizeLongSpec.longListSample_reachable
private noncomputable abbrev _rlp_item_size_routine_witness :=
  @EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_item_size_spec_within
private noncomputable abbrev _rlp_item_span_routine_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.rlp_item_span_spec_within
-- #10780: the long outer-header arm, the total dispatch, and the long arm's
-- non-vacuity trio (coverRef plus two negative controls).
private noncomputable abbrev _rlp_item_span_long_routine_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.rlp_item_span_long_spec_within
private noncomputable abbrev _rlp_item_span_any_header_routine_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.rlp_item_span_any_header_spec_within
private noncomputable abbrev _rlp_item_span_long_cover_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.rlp_item_span_long_precondition_reachable
private noncomputable abbrev _rlp_item_span_long_bundle_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.rlp_item_span_long_bundle_satisfiable
private noncomputable abbrev _rlp_item_span_long_gate_negative_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.long_gate_negative_control
private noncomputable abbrev _rlp_item_span_long_walk_negative_witness :=
  @EvmAsm.Codegen.RlpItemSpanSpec.long_walk_negative_control
-- #12033: the strict-wrapper machine tie and its compiled satisfying instance.
private noncomputable abbrev _rlp_walk_next_shared_strict_routine_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictTie.rlp_walk_next_shared_nonlist_strict_spec_within
private noncomputable abbrev _rlp_walk_next_shared_strict_instance_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictTie.rlp_walk_next_shared_nonlist_strict_instance
private noncomputable abbrev _rlp_walk_next_shared_strict_bridge_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictTie.strictW_of_rlpItemDecode_nonlist
-- #12799 rows 3 and 8: the two own-anchored entry contracts.
private noncomputable abbrev _rlp_walk_next_entry_routine_witness :=
  @EvmAsm.Codegen.RlpWalkNextEntryTie.rlp_walk_next_entry_nonlist_strict_spec_within
private noncomputable abbrev _rlp_walk_next_entry_instance_witness :=
  @EvmAsm.Codegen.RlpWalkNextEntryTie.rlp_walk_next_entry_instance
private noncomputable abbrev _rlp_walk_next_entry_accept_witness :=
  @EvmAsm.Codegen.RlpWalkNextEntryTie.rlp_walk_next_entry_accept_reachable
private noncomputable abbrev _rlp_walk_next_entry_refutable_witness :=
  @EvmAsm.Codegen.RlpWalkNextEntryTie.rlp_walk_next_entry_hyps_refutable
private noncomputable abbrev _rlp_walk_next_entry_budget_witness :=
  @EvmAsm.Codegen.RlpWalkNextEntryTie.budget_ge_two
-- #12799 row 4: the leaf-only wrapper, its two path instances, the deadness
-- lemma's own instance, and the negative control.
private noncomputable abbrev _rlp_walk_next_leaf_routine_witness :=
  @EvmAsm.Codegen.RlpWalkNextLeafTie.rlp_walk_next_leaf_entry_nonlist_strict_spec_within
private noncomputable abbrev _rlp_walk_next_leaf_instance_witness :=
  @EvmAsm.Codegen.RlpWalkNextLeafTie.rlp_walk_next_leaf_entry_instance
private noncomputable abbrev _rlp_walk_next_leaf_single_byte_witness :=
  @EvmAsm.Codegen.RlpWalkNextLeafTie.rlp_walk_next_leaf_single_byte_instance
private noncomputable abbrev _rlp_walk_next_leaf_dead_arm_witness :=
  @EvmAsm.Codegen.RlpWalkNextLeafTie.prefix_test_always_taken
private noncomputable abbrev _rlp_walk_next_leaf_dead_arm_instance_witness :=
  @EvmAsm.Codegen.RlpWalkNextLeafTie.rlp_walk_next_leaf_prefix_test_instance
private noncomputable abbrev _rlp_walk_next_leaf_refutable_witness :=
  @EvmAsm.Codegen.RlpWalkNextLeafTie.rlp_walk_next_leaf_premises_refutable
-- #12799 row 5 (PARTIAL): the shared exit, the four length arms, the 22-probe
-- dispatch, their instances and the negative control.  Witnessed here so the
-- axiom gate sees them -- naming a theorem in a `notes :=` string puts it in NO
-- gate, the hole found three times this week.
private noncomputable abbrev _arity_epilogue_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.epilogue_spec_within
private noncomputable abbrev _arity_fail_exit_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.fail_exit_spec_within
private noncomputable abbrev _arity_ok_exit_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.ok_exit_spec_within
private noncomputable abbrev _arity_fail_exit_instance_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.fail_exit_instance
private noncomputable abbrev _arity_ok_exit_instance_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.ok_exit_instance
private noncomputable abbrev _arity_len_arm_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.len_check_arm_within
private noncomputable abbrev _arity_len_arm_32_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.len_arm_32_within
private noncomputable abbrev _arity_len_arm_20_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.len_arm_20_within
private noncomputable abbrev _arity_len_arm_256_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.len_arm_256_within
private noncomputable abbrev _arity_len_arm_8_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.len_arm_8_within
private noncomputable abbrev _arity_dispatch_probe_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_probe_within
private noncomputable abbrev _arity_dispatch_step_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_step
private noncomputable abbrev _arity_dispatch_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_spec_within
private noncomputable abbrev _arity_dispatch_instance_6_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_instance_6
private noncomputable abbrev _arity_dispatch_instance_12_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_instance_12
private noncomputable abbrev _arity_dispatch_target_values_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatchTarget_values
private noncomputable abbrev _arity_extent_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.arity_extent
private noncomputable abbrev _arity_refutable_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.arity_premises_refutable
private noncomputable abbrev _arity_dispatch_then_arm_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_then_arm_within
private noncomputable abbrev _arity_dispatch_then_arm_6_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_then_arm_6
private noncomputable abbrev _arity_dispatch_then_arm_0_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.dispatch_then_arm_0
private noncomputable abbrev _arity_gate_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.arity_gate_within
private noncomputable abbrev _arity_loop_guard_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.loop_guard_within
private noncomputable abbrev _arity_loop_backedge_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.loop_backedge_within
private noncomputable abbrev _arity_loop_measure_witness :=
  @EvmAsm.Codegen.HeaderArityCheckTie.loop_measure_decreases
-- The `hll`-redundancy bridge lives beside the theorem it is about
-- (`lane-b4` 6925938c9); witness it from here so the axiom gate sees it.
private noncomputable abbrev _rlp_walk_next_hll_redundant_witness :=
  @EvmAsm.Codegen.RlpWalkNextEntryTie.ult_f8_of_ult_c0
private noncomputable abbrev _rlp_walk_init_entry_routine_witness :=
  @EvmAsm.Codegen.RlpWalkInitTie.rlp_walk_init_entry_spec_within
private noncomputable abbrev _rlp_walk_init_entry_instance_witness :=
  @EvmAsm.Codegen.RlpWalkInitTie.rlp_walk_init_entry_instance
private noncomputable abbrev _rlp_walk_init_entry_refutable_witness :=
  @EvmAsm.Codegen.RlpWalkInitTie.rlp_walk_init_entry_hyps_refutable
-- #12300: strict LIST-cycle witnesses.  The structural family is closed by
-- `mutual_fuel_witness`; the two CPS rows retain their explicit adapter
-- premises until the machine continuation is derived from that family.
private noncomputable abbrev _rlp_validate_payload_cycle_routine_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictFuel.rlp_validate_payload_cps_under_shared
private noncomputable abbrev _rlp_walk_next_shared_cycle_routine_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictFuel.shared_list_arm_contract_from_adapter
private noncomputable abbrev _rlp_cycle_fuel_mutual_witness :=
  @EvmAsm.Codegen.RlpWalkNextStrictFuel.mutual_fuel_witness
-- #10780 item 1, at every width. `long2_first_length_byte_ne_zero` is the `lenlen = 2`
-- instance and is stated over the literal shift `len >>> 8`, so it says nothing at any
-- other width; this is the property itself, over `u64ByteLen`. Witnessed because the
-- `lenlen >= 3` arm will consume it as a specification, and a specification outside the
-- axiom gate is the #11637 failure mode -- the same reason the `LongSpan` lemmas are
-- gated. No registry row changes: this is a side condition, not a routine triple.
-- #11517 (template pair): the account-leaf sentinels. Both `EMPTY_CODE_HASH` and
-- `EMPTY_TRIE_ROOT` now have kernel-checked SpecRef ties through split Keccak proofs.
-- The literal pins remain gated so CI also rechecks their byte values.
-- #10780: the length-byte loop of `rlp_encode_list_prefix` at a SYMBOLIC trip count,
-- which is what the `lenlen >= 3` arms were missing. Ported from `rebLolLoop` (same five
-- instructions, registers renamed), so the ~200-lines-per-byte unrolling cost the long2
-- header warns about does not have to be paid. Witnessed rather than left for the arm
-- that consumes it: this is a machine result about the emitted program, and it is the
-- piece a later composition will trust without re-checking. No registry row changes --
-- a block lemma, not a routine triple.
-- #10780: `rlp_item_size`'s long-form length-byte ACCUMULATION loop (idx25-31) at a
-- symbolic trip count -- the read/accumulate counterpart of `lpLolLoop`'s write/extract.
-- Ported from `wi_len_loop` (`rlp_walk_init` idx17-23): the same seven instructions with
-- counter x30/x30, accumulator x31/x28, scratch x28/x31, cursor x6/x29. This is the
-- machine half the `SpanForm` long arms need; the model half is already gated as the
-- `LongSpan` lemmas. ⚠️ The drift guard is witnessed WITH it on purpose: the loop is
-- proved core-side over a second copy of `rlpItemSize_prog` (core may not import Codegen),
-- so the guard is the only thing keeping the copy and the emitted program in step.
private noncomputable abbrev _rlp_item_size_len_loop_witness :=
  @EvmAsm.Rv64.RLP.risLenLoop
private noncomputable abbrev _rlp_item_size_len_loop_body_witness :=
  @EvmAsm.Rv64.RLP.risLenLoopBody
private noncomputable abbrev _rlp_item_size_prog_drift_guard_witness :=
  @EvmAsm.Codegen.rlpItemSize_prog_eq_verified_prog
private noncomputable abbrev _rlp_prefix_lol_loop_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLoopSpec.lpLolLoop
private noncomputable abbrev _rlp_prefix_lol_body_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLoopSpec.lpLolBody
private noncomputable abbrev _rlp_prefix_loop_writes_toBytesBE_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLoopSpec.lpLoop_writes_toBytesBE
-- #10817: `bal_canonical_sort`'s canonical nibble extractor (flat indices 67-94,
-- `base+268 -> base+380`), proved to agree with a key decoded from the FIELD
-- SEMANTICS rather than from the sorter's own segment descriptor. That direction is
-- the whole point: a descriptor-derived key would let a limb swap satisfy both
-- sortedness and permutation-preservation, which is exactly why
-- `BalCanonicalSort.lean:41-44` refuses to substitute either property. Witnessed
-- rather than left to the sortedness theorem that will consume it -- the same
-- discipline as `lpLolLoop`, and for the same reason: a specification outside the
-- axiom gate is the #11637 failure mode. The model side is witnessed WITH the
-- machine side, because a key definition that drifted from the reversal it encodes
-- would silently re-open the vacuity. No registry row changes: a block lemma over
-- a pc range, not a routine triple, and no `JALR`.
private noncomputable abbrev _bal_digit_agree_1seg_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigitAgree_1seg
private noncomputable abbrev _bal_digit_agree_2seg_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigitAgree_2seg
private noncomputable abbrev _bal_digit_agree_2seg_live_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigitAgree_2seg_live
private noncomputable abbrev _bal_digit_at_67_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balDigit_at_67
private noncomputable abbrev _bal_key_getD_head_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balCanonicalKey_getD_head
private noncomputable abbrev _bal_key_getD_tail_witness :=
  @EvmAsm.Codegen.BalCanonicalSortDigitSpec.balCanonicalKey_getD_tail
-- #11517 (template pair): the account-leaf sentinels, pinned. `EMPTY_TRIE_ROOT` /
-- `EMPTY_CODE_HASH` existed in three unconnected copies -- SpecRef's computed pair and two
-- baked asm literals -- so a typo in one typechecked everywhere and produced a wrong state
-- root. These are the ties. Gated deliberately: the value of a drift pin is that CI
-- rechecks it, and a pin outside the gate is a comment.
-- #11517 (template pair): the account-leaf sentinels. `EMPTY_CODE_HASH` now has a
-- kernel-checked SpecRef tie through the split Keccak proof; the trie-root copy remains a
-- numeral drift pin because its distinct `keccak256 [0x80]` KAT would need a separately
-- justified intrinsic-depth theorem. The pins stay gated so CI rechecks the remaining
-- literal correspondence.
-- #11517: the `Stateless/Constants.lean` hex-`String` copies, pinned to the byte-list
-- copies #12032 pinned. The `eq_adBytes`/`eq_aieBytes` ties are the strongest of the set:
-- two independent asm-side definitions in two different representations, equal outright,
-- with no keccak and no written numeral in between.
private noncomputable abbrev _keccak256EmptyHashHex_eq_adBytes_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.keccak256EmptyHashHex_eq_adBytes
private noncomputable abbrev _keccak256EmptyHashHex_eq_aieBytes_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.keccak256EmptyHashHex_eq_aieBytes
private noncomputable abbrev _emptyTrieRootHex_eq_adBytes_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.emptyTrieRootHex_eq_adBytes
private noncomputable abbrev _trieRoot_ne_codeHash_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.trieRoot_ne_codeHash
-- ✅ #12081 REPAIRED: `emptyOmmerHashHex` now holds the empty ommer hash (keccak of
-- rlp([]) = keccak(0xc0)); it previously aliased the empty trie root. The divergence
-- was pinned as `divergence_emptyOmmerHashHex` by #12082 and retired by #12081; the
-- registry keeps a row pointing at the fix pin so the record does not vanish.
private noncomputable abbrev _fix_emptyOmmerHashHex_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.fix_emptyOmmerHashHex
-- #11517: SpecRef-derived vs asm-flattened numbers -- the sharpest drift shape, since a
-- repricing moves the SpecRef side silently while the asm literal stays put.
private noncomputable abbrev _bvEip7702AuthRegularGas_eq_spec_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.bvEip7702AuthRegularGas_eq_spec
private noncomputable abbrev _maxInitcodeSize_eq_spec_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.maxInitcodeSize_eq_spec
private noncomputable abbrev _maxDeployedCodeSize_eq_spec_witness :=
  @EvmAsm.Codegen.SpecRefConstantPins.maxDeployedCodeSize_eq_spec
private noncomputable abbrev _ad_empty_trie_root_value_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyTrieRootBytes_value
private noncomputable abbrev _ad_empty_code_hash_value_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyCodeHashBytes_value
private noncomputable abbrev _ad_empty_code_hash_spec_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyCodeHashBytes_eq_spec
private noncomputable abbrev _ad_empty_trie_root_spec_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyTrieRootBytes_eq_spec
private noncomputable abbrev _aie_empty_code_hash_value_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.aieEmptyCodeHashBytes_value
private noncomputable abbrev _ad_empty_code_hash_eq_aie_witness :=
  @EvmAsm.Codegen.AccountDecodeCorrespondence.adEmptyCodeHashBytes_eq_aie
private noncomputable abbrev _rlp_prefix_first_length_byte_ne_zero_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixCanonical.first_length_byte_ne_zero
private noncomputable abbrev _rlp_prefix_pow_le_u64ByteLen_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixCanonical.pow_le_u64ByteLen
-- #11795: the REFUTATION of `RlpWalkNextStrict`, plus the accept-indexed bridge that
-- replaces it. Neither changes a registry row -- witnessed because a negative control is
-- only worth what its axioms are, and this one is load-bearing for the issue's
-- sequencing: it is what says the residual is FALSE rather than open, so nobody schedules
-- a proof against it. The replacement is witnessed alongside so the correction and its
-- repair cannot drift apart.
private noncomputable abbrev _not_rlpWalkNextStrict_witness :=
  @EvmAsm.Codegen.RlpListCountItemsBridge.not_rlpWalkNextStrict_nestedNonCanonical
private noncomputable abbrev _rlpItemDecodeBridgesOn_of_accepts_witness :=
  @EvmAsm.Codegen.RlpListCountItemsBridge.rlpItemDecodeBridgesOn_of_accepts
private noncomputable abbrev _rlpItemDecodeStrictW_of_decodeAux_witness :=
  @EvmAsm.Rv64.RLP.rlpItemDecodeStrictW_of_decodeAux
private noncomputable abbrev _account_rlp_walk_init_routine_witness :=
  @EvmAsm.Evm64.account_rlp_walk_init_spec_within
private noncomputable abbrev _rlp_walk_init_long1_routine_witness :=
  @EvmAsm.Evm64.rlp_walk_init_long1_spec_within
private noncomputable abbrev _account_rlp_walk_next_field0_routine_witness :=
  @EvmAsm.Evm64.account_rlp_walk_next_field0_spec_within
private noncomputable abbrev _account_rlp_walk_next_field1_routine_witness :=
  @EvmAsm.Evm64.account_rlp_walk_next_field1_spec_within
private noncomputable abbrev _rlp_walk_next_scalar_routine_witness :=
  @EvmAsm.Evm64.rlp_walk_next_scalar_spec_within
private noncomputable abbrev _account_rlp_content_to_u64_nonce_routine_witness :=
  @EvmAsm.Evm64.account_rlp_content_to_u64_nonce_spec_within
private noncomputable abbrev _account_extract_nonce_routine_witness :=
  @EvmAsm.Codegen.account_extract_nonce_spec_within
private noncomputable abbrev _account_rlp_content_to_u256_be_balance_routine_witness :=
  @EvmAsm.Evm64.account_rlp_content_to_u256_be_balance_spec_within
-- #12799 rows 1 and 2: the anchored triples, plus BOTH non-vacuity witnesses for
-- each. The instance and the negative control get their own abbrevs deliberately
-- — a contract nobody can instantiate proves nothing, and a hypothesis bundle
-- nobody can falsify excludes nothing, so the axiom gate must audit all four
-- rather than only the two triples.
private noncomputable abbrev _rlp_content_to_u64_strict_routine_witness :=
  @EvmAsm.Codegen.RlpContentStrictAtGuest.rlp_content_to_u64_strict_at_guest_spec_within
private noncomputable abbrev _rlp_content_to_u64_strict_instance_witness :=
  @EvmAsm.Codegen.RlpContentStrictAtGuest.rlp_content_to_u64_strict_at_guest_instance
private noncomputable abbrev _rlp_content_to_u64_strict_negctl_witness :=
  @EvmAsm.Codegen.RlpContentStrictAtGuest.rlp_content_to_u64_strict_at_guest_negative_control
private noncomputable abbrev _rlp_content_to_u256_be_strict_routine_witness :=
  @EvmAsm.Codegen.RlpContentStrictAtGuest.rlp_content_to_u256_be_strict_at_guest_spec_within
private noncomputable abbrev _rlp_content_to_u256_be_strict_instance_witness :=
  @EvmAsm.Codegen.RlpContentStrictAtGuest.rlp_content_to_u256_be_strict_at_guest_instance
private noncomputable abbrev _rlp_content_to_u256_be_strict_negctl_witness :=
  @EvmAsm.Codegen.RlpContentStrictAtGuest.rlp_content_to_u256_be_strict_at_guest_negative_control
-- #11289: the 7 specs `Correspondence.lean` named but nothing witnessed.
private noncomputable abbrev _rlp_bytes_encoded_size_routine_witness :=
  @EvmAsm.Codegen.RlpBytesEncodedSizeSAsm.rlpBytesEncodedSize_spec
-- #11341: the model-facing counterpart, named by the `.bridged` Correspondence row.
private noncomputable abbrev _rlp_bytes_encoded_size_encode_routine_witness :=
  @EvmAsm.Codegen.RlpBytesEncodedSizeSAsm.rlpBytesEncodedSize_encode_spec
private noncomputable abbrev _rlp_field_to_u64_routine_witness :=
  @EvmAsm.Codegen.RlpFieldToU64SAsm.rlpFieldToU64_spec_within
-- #12386: the production entry was retired, but Correspondence.lean still
-- records the offline Program/spec relation. Keep that relation in the axiom
-- gate through this Codegen-side witness; Correspondence.lean deliberately
-- does not import Codegen.
private noncomputable abbrev _rlp_field_to_u256_be_correspondence_witness :=
  @EvmAsm.Codegen.RlpFieldToU256BeSAsm.rlpFieldToU256Be_spec_within
private noncomputable abbrev _rlp_field_to_u64_strict_routine_witness :=
  @EvmAsm.Codegen.RlpFieldToU64StrictSAsm.rlpFieldToU64_spec_within
private noncomputable abbrev _header_validate_extra_data_length_routine_witness :=
  @EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.header_validate_extra_data_length_spec_within
-- #11575 row 2's Correspondence row names this; Codegen-side, so it lives here.
private noncomputable abbrev _header_extra_data_length_of_decode_witness :=
  @EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.header_extra_data_length_of_decode
private noncomputable abbrev _headers_parent_hash_routine_witness :=
  @EvmAsm.Codegen.headers_parent_hash_spec_within
-- #12799 non-vacuity for `headersParentHash_out_length`, the lemma that
-- retired the hvph `hOutLen` gate: a SATISFIABLE instance reaching the
-- success branch (so the saturating `take 32` is exercised, not the trivial
-- passthrough) and a NEGATIVE CONTROL where `hclaimed` is false and the
-- conclusion fails with it.
private noncomputable abbrev _headers_parent_hash_out_length_witness :=
  @EvmAsm.Codegen.headersParentHash_out_length
private noncomputable abbrev _headers_parent_hash_out_length_sat_witness :=
  @EvmAsm.Codegen.hphSampleHeader_reaches_success
private noncomputable abbrev _headers_parent_hash_out_length_neg_witness :=
  @EvmAsm.Codegen.headersParentHash_out_length_refutable_without_hclaimed

private noncomputable abbrev _header_validate_parent_hash_routine_witness :=
  @EvmAsm.Codegen.HeaderValidateParentHashSpec.header_validate_parent_hash_spec_within
-- #12799: the dispatcher's three full-premise covers. Each instantiates EVERY
-- static premise simultaneously with live data and lands on a DIFFERENT arm
-- (status 1 / status 0 / first-differing dword 2), so no arm of the three-way
-- post is reachable only in the large. They existed but were in no gate.
private noncomputable abbrev _header_validate_parent_hash_extract_fail_cover_witness :=
  @EvmAsm.Codegen.HeaderValidateParentHashSpec.header_validate_parent_hash_extract_fail_cover
private noncomputable abbrev _header_validate_parent_hash_match_cover_witness :=
  @EvmAsm.Codegen.HeaderValidateParentHashSpec.header_validate_parent_hash_match_cover
private noncomputable abbrev _header_validate_parent_hash_mismatch2_cover_witness :=
  @EvmAsm.Codegen.HeaderValidateParentHashSpec.header_validate_parent_hash_mismatch2_cover
private noncomputable abbrev _header_extract_logs_bloom_routine_witness :=
  @EvmAsm.Codegen.HeaderExtractLogsBloomSpec.headerExtractLogsBloom_spec_within
-- Correspondence row (#11575) names this; Codegen-side, so the witness lives here
-- for the same reason as #11351's below.
private noncomputable abbrev _header_logs_bloom_of_decode_witness :=
  @EvmAsm.Codegen.HeaderExtractLogsBloomSpec.header_logs_bloom_of_decode
private noncomputable abbrev _header_extract_number_routine_witness :=
  @EvmAsm.Codegen.HeaderExtractNumberSpec.header_extract_number_spec_within
-- #12313: flat guest-image specializations of the three root-extract fnspecs.
private noncomputable abbrev _validate_header_routine_witness :=
  @EvmAsm.Codegen.validateHeaderFunction_eq_prog
private noncomputable abbrev _header_extract_state_root_routine_witness :=
  @EvmAsm.Codegen.HeaderFieldsSpec.header_extract_state_root_spec_within
private noncomputable abbrev _header_extract_receipts_root_routine_witness :=
  @EvmAsm.Codegen.HeaderReceiptsRootSpec.header_extract_receipts_root_spec_within
private noncomputable abbrev _header_extract_withdrawals_root_routine_witness :=
  @EvmAsm.Codegen.HeaderWithdrawalsRootSpec.header_extract_withdrawals_root_spec_within
private noncomputable abbrev _header_extended_decode_u64_segment_routine_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_segment_spec_within
-- #12799: the six anchored, callee-composed per-site corollaries. Five are
-- cited by rows above; `_444` is witnessed but unrowed (see the note there),
-- so the axiom gate still audits it. The two non-vacuity obligations are
-- witnessed alongside, per the "degenerate inhabitant + negative control"
-- rule: an instance discharging every hypothesis and landing in the ACCEPT
-- disjunct, and a control where the same conjuncts are provably FALSE.
private noncomputable abbrev _hed_u64_site_324_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_324_spec_within
private noncomputable abbrev _hed_u64_site_364_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_364_spec_within
private noncomputable abbrev _hed_u64_site_404_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_404_spec_within
private noncomputable abbrev _hed_u64_site_444_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_444_spec_within
private noncomputable abbrev _hed_u64_site_604_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_604_spec_within
private noncomputable abbrev _hed_u64_site_644_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_644_spec_within
private noncomputable abbrev _hed_u64_site_composed_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_composed_within
private noncomputable abbrev _hed_u64_site_instance_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_instance
private noncomputable abbrev _hed_u64_site_negative_control_witness :=
  @EvmAsm.Codegen.HeaderU64ExtractSpec.header_extended_decode_u64_site_negative_control
-- #12799 ownership row 6, the two layers rowed above plus their non-vacuity
-- obligations. The copy loop is proved ONCE and instantiated at both sites, so
-- `copy_loop_spec_within` is witnessed alongside the two anchored corollaries;
-- likewise `walk_next_site_composed_within` is the composition step and the
-- nineteen anchored sites are its instances. Only two of the nineteen are
-- witnessed here (the first and the last) — they share one proof term, and
-- `lake exe axiomsweep --check` sweeps the other seventeen as ordinary
-- `EvmAsm.*` declarations.
private noncomputable abbrev _hed_copy_loop_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeCopy.copy_loop_spec_within
private noncomputable abbrev _hed_parent_hash_copy_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeCopy.parent_hash_copy_spec_within
private noncomputable abbrev _hed_state_root_copy_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeCopy.state_root_copy_spec_within
private noncomputable abbrev _hed_parent_hash_copy_instance_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeCopy.parent_hash_copy_instance
private noncomputable abbrev _hed_state_root_copy_instance_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeCopy.state_root_copy_instance
private noncomputable abbrev _hed_copy_content_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeCopy.parent_hash_copy_content
private noncomputable abbrev _hed_copy_negative_control_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeCopy.copy_loop_hyps_refutable
private noncomputable abbrev _hed_walk_init_site_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walk_init_site_spec_within
private noncomputable abbrev _hed_walk_init_site_instance_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walk_init_site_instance
private noncomputable abbrev _hed_init_disjoint_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.decoder_init_disjoint
private noncomputable abbrev _hed_walk_site_composed_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walk_next_site_composed_within
private noncomputable abbrev _hed_walk_site_56_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walk_next_site_56_spec_within
private noncomputable abbrev _hed_walk_site_624_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walk_next_site_624_spec_within
private noncomputable abbrev _hed_walk_disjoint_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.decoder_walk_disjoint
private noncomputable abbrev _hed_walk_pre_instance_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walkPre_instance
private noncomputable abbrev _hed_walk_site_instance_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walk_next_site_56_instance
private noncomputable abbrev _hed_walk_gate_refutable_list_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walkPre_refutable_on_list
private noncomputable abbrev _hed_walk_gate_refutable_empty_witness :=
  @EvmAsm.Codegen.HeaderExtendedDecodeWalkSite.walkPre_refutable_on_empty_span
-- #11575 tier A. Namespace note: both theorems live in the `…Spec` NAMESPACE
-- (`ChainValidateConsecutiveNumbersSpec`) but in the `…LoopClose` MODULE — the
-- loop-close files reopen the spec namespace rather than declaring their own.
-- #11576: the seventh header-family routine — the one `docs/leaf-routine-targets.md`
-- singles out as NOT a mechanical fork, because it had only the string↔Program
-- byte-identity theorem and no triple at all. Domain-restricted to the empty header list
-- (`hN : encoded = []`), with the restriction IN the statement; the `N ≥ 1` loop is the
-- named remaining half. No registry row yet: a row would advertise coverage of a routine
-- whose loop is unproven, and the six exit-path lemmas are the honest unit until then.
-- `nonce_rule_agrees` is witnessed because it settles the canonical-scalar leniency
-- question — on an 8-byte field the guest's `u64 = 0` test IS the port's all-zero test.
private noncomputable abbrev _cvpmf_empty_routine_witness :=
  @EvmAsm.Codegen.ChainValidatePostMergeFullSpec.chain_validate_post_merge_full_spec_within_empty
private noncomputable abbrev _cvpmf_nonce_rule_agrees_witness :=
  @EvmAsm.Codegen.ChainValidatePostMergeFullSpec.nonce_rule_agrees
private noncomputable abbrev _cvpmf_empty_ommer_hash_value_witness :=
  @EvmAsm.Codegen.ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_value
private noncomputable abbrev _header_validate_post_merge_routine_witness :=
  @EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec.header_validate_post_merge_spec_within
-- #12346 Step 3: the positive K67 arm is tied to the Amsterdam decoder under
-- an explicit decode-success premise; keep the bridge in the axiom gate even
-- though it is not a second whole-routine registry row.
private noncomputable abbrev _header_validate_post_merge_decode_bridge_witness :=
  @EvmAsm.Codegen.HeaderValidatePostMergeCorrespondenceBridge.k67GuardOk_decode_header
private noncomputable abbrev _header_validate_post_merge_guard_constructive_witness :=
  @EvmAsm.Codegen.HeaderValidatePostMergeCorrespondenceBridge.k67GuardOk_constructive_witness
-- #11925 continuation: whole-routine triples surfaced by scripts/proof-frontier.py.
-- Namespace/molecule note (mirrors the twins): account_extract_balance_spec_within
-- lives in the bare `EvmAsm.Codegen` NAMESPACE inside AccountAccessorTopSpec.lean;
-- account_decode_spec_within is in `EvmAsm.Codegen.AccountDecodeSpec` inside
-- AccountDecodeClose6.lean; the other two follow the `…Spec` namespace convention.
private noncomputable abbrev _account_decode_routine_witness :=
  @EvmAsm.Codegen.AccountDecodeSpec.account_decode_spec_within
private noncomputable abbrev _account_extract_balance_routine_witness :=
  @EvmAsm.Codegen.account_extract_balance_spec_within
private noncomputable abbrev _account_is_eip161_empty_routine_witness :=
  @EvmAsm.Codegen.AccountIsEip161EmptySpec.account_is_eip161_empty_spec_within
private noncomputable abbrev _receipt_extract_logs_bloom_routine_witness :=
  @EvmAsm.Codegen.ReceiptExtractLogsBloomSpec.receiptExtractLogsBloom_spec_within
-- Correspondence row #11351 names this; it is Codegen-side, and Correspondence
-- deliberately does not import Codegen, so the witness abbrev lives here.
private noncomputable abbrev _header_number_of_decode_witness :=
  @EvmAsm.Codegen.HeaderExtractNumberSpec.header_number_of_decode
-- #11345: the model-facing consumer joining `account_decode`'s output struct to
-- `AccountRecord` and thence to `SpecRef.decode_account_from_leaf`. Codegen-side,
-- so like the #11351 witness above it lives here rather than in Correspondence.
-- #11516: named by the `account_decode` Correspondence row. Codegen-side, so the
-- witness lives here (same reason as the #11351/#11345/#11348 witnesses above).
-- Row without witness = theorem invisible to the axiom gate; that is a separate
-- obligation from claiming a tier, and #11348 is where I learned it the hard way.
private noncomputable abbrev _account_decode_spec_within_witness :=
  @EvmAsm.Codegen.AccountDecodeSpec.account_decode_spec_within
private noncomputable abbrev _account_decode_matches_specRef_witness :=
  @EvmAsm.Codegen.AccountDecodeCompose.decoded_matches_specRef
private noncomputable abbrev _account_decode_output_witness :=
  @EvmAsm.Codegen.AccountDecodeCompose.outputSuccess_eq_accountDecodedIs
-- #11346 item 2: the leniency agreement now consumes the shared `beAccum`
-- model directly; no duplicate-definition identity witness is needed.
private noncomputable abbrev _account_eip161_leniency_witness :=
  @EvmAsm.Codegen.AccountIsEip161EmptySpec.leniency_agrees
-- #11348: Correspondence's `bloom_or_into` row names this, and it is Codegen-side,
-- so like the #11351/#11345 witnesses above the abbrev lives here.
--
-- ⚠️ NO `RoutineEntry` row accompanies it, deliberately. Every row in the registry
-- above claims a FLAT whole-routine triple at `GuestAddrs.<symbol>`, derived by
-- `Fn.retSpecFlat`; `bloomOrIntoFn_spec` is the structured SAsm `.Spec`, so a
-- `.proven` row would overclaim. The WITNESS is what puts a theorem in the axiom
-- gate; the ROW is what claims a tier. Those are separate obligations and only the
-- first is warranted here. (This distinction is the subject of #11637.)
private noncomputable abbrev _bloom_or_into_witness :=
  @EvmAsm.Codegen.BloomOrIntoSAsm.bloomOrIntoFn_spec
-- The reference-facing half: why per-receipt accumulation matches a `logs_bloom`
-- computed from the flat log list.
private noncomputable abbrev _bloom_or_into_fold_witness :=
  @EvmAsm.Codegen.BloomOrIntoSAsm.bloomOrInto_fold_eq_logs_bloom
private noncomputable abbrev _rlp_list_encoded_size_routine_witness :=
  @EvmAsm.Codegen.RlpListEncodedSizeSAsm.rlpListEncodedSize_spec
-- #11341: the model-facing counterpart, named by the `.bridged` Correspondence row.
private noncomputable abbrev _rlp_list_encoded_size_encode_routine_witness :=
  @EvmAsm.Codegen.RlpListEncodedSizeSAsm.rlpListEncodedSize_encode_spec
private noncomputable abbrev _rlp_list_nth_item_routine_witness :=
  @EvmAsm.Codegen.RlpListNthItemSAsm.rlpListNthItem_spec_within
private noncomputable abbrev _rlp_list_count_items_routine_witness :=
  @EvmAsm.Codegen.RlpListCountItemsSAsm.rlp_list_count_items_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_short_routine_witness :=
  @EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_short_pinned_spec_within
-- #10780: the long1 arm, proven since the short arm landed but never registered.
private noncomputable abbrev _rlp_encode_list_prefix_long1_routine_witness :=
  @EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_long1_pinned_spec_within
-- #10780 item 3: the long2 arm, plus its canonical-form lemma (the no-leading-zero
-- property in the length-of-length, which is what makes the header valid RLP).
private noncomputable abbrev _rlp_encode_list_prefix_long2_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong2Spec.rlp_encode_list_prefix_long2_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long2_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong2Spec.long2_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long3_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong3Spec.rlp_encode_list_prefix_long3_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long3_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong3Spec.long3_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long4_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong4Spec.rlp_encode_list_prefix_long4_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long4_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong4Spec.long4_first_length_byte_ne_zero
-- #10780 item 3, widths 5/6/7. Each triple is witnessed alongside its canonicality
-- instance for the same reason long3/long4 are: the instance is what makes the emitted
-- header canonical RLP rather than merely parseable, and a specification outside the
-- axiom gate is the #11637 failure mode.
private noncomputable abbrev _rlp_encode_list_prefix_long5_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong5Spec.rlp_encode_list_prefix_long5_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long5_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong5Spec.long5_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long6_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong6Spec.rlp_encode_list_prefix_long6_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long6_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong6Spec.long6_first_length_byte_ne_zero
private noncomputable abbrev _rlp_encode_list_prefix_long7_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong7Spec.rlp_encode_list_prefix_long7_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long7_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong7Spec.long7_first_length_byte_ne_zero
-- #10780 width 8, the last arm: with it the ladder is covered at every width
-- `u64ByteLen` can produce, so widths 1-8 are exhaustive over `len : Word`.
private noncomputable abbrev _rlp_encode_list_prefix_long8_routine_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong8Spec.rlp_encode_list_prefix_long8_pinned_spec_within
private noncomputable abbrev _rlp_encode_list_prefix_long8_canonical_witness :=
  @EvmAsm.Codegen.RlpEncodeListPrefixLong8Spec.long8_first_length_byte_ne_zero
-- #11291: the whole-routine withdrawal decoder (existed since #10782).
private noncomputable abbrev _bgv_u32le_routine_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashBgvOffset.bgv_u32le_offset_spec_within
private noncomputable abbrev _check_gas_limit_routine_witness :=
  @EvmAsm.Codegen.CheckGasLimitSAsm.checkGasLimit_ref_spec
private noncomputable abbrev _bytes_to_nibbles_routine_witness :=
  @EvmAsm.Codegen.BytesToNibblesSAsm.bytesToNibblesFlat_spec
-- #11799 dep: whole-routine mpt_node_kind machine triple.
private noncomputable abbrev _mpt_node_kind_routine_witness :=
  @EvmAsm.Codegen.MptNodeKindSpec.mpt_node_kind_spec_within
-- #12027: Result → kindTag wiring under WF (success arms + constructive existence).
private noncomputable abbrev _mpt_node_kind_result_eq_kindTag_witness :=
  @EvmAsm.Codegen.MptNodeKindWire.mptNodeKindResult_eq_kindTag
private noncomputable abbrev _mpt_node_kind_result_exists_kindTag_witness :=
  @EvmAsm.Codegen.MptNodeKindWire.mptNodeKindResult_exists_kindTag

-- #11799 residual audit: hp_decode_nibbles machine already existed; register it.
private noncomputable abbrev _hp_decode_nibbles_routine_witness :=
  @EvmAsm.Codegen.HpDecodeNibblesSAsm.hp_decode_nibbles_spec_ported
private noncomputable abbrev _withdrawal_decode_routine_witness :=
  @EvmAsm.Codegen.WithdrawalDecodeSpec.withdrawal_decode_spec_within
-- #11574: the two field-bound scans. The MACHINE triples were unwitnessed by
-- `check-axioms.sh` until now despite predating this registration by months —
-- exactly the "witnessed symbol with no row" / "row with no witness" pair of
-- omissions #11342 and #11348 each caught once.
private noncomputable abbrev _u256_sub_be_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldReduceOnceSAsm.u256SubBeFlat_spec
private noncomputable abbrev _u256_lt_be_routine_witness :=
  @EvmAsm.Codegen.U256LtBeSAsm.u256LtBe_spec
-- #12628: third instance of "proven is not gate-verified", and the first
-- consumed one — K73/K74 call this via `header_base_fee` while it carried no
-- registry row, so the axiom gate (which runs over registered witnesses
-- only) never audited it.
private noncomputable abbrev _u256_eq_routine_witness :=
  @EvmAsm.Codegen.U256EqSAsm.u256Eq_spec
-- #12244: the two u256 BE members lifted/anchored to flat triples this pass.
private noncomputable abbrev _u256_add_be_routine_witness :=
  @EvmAsm.Codegen.U256BeFlat.u256AddBeFlat_spec
private noncomputable abbrev _u256_is_zero_routine_witness :=
  @EvmAsm.Codegen.Proofs.u256IsZeroFlat_spec
private noncomputable abbrev _u256_from_u64_be_routine_witness :=
  @EvmAsm.Codegen.U256BeFlat.u256FromU64BeFlat_spec
private noncomputable abbrev _u256_mul_u64_be_routine_witness :=
  @EvmAsm.Codegen.U256MulU64Be.mulWhole_spec
private noncomputable abbrev _u256_mul_u64_be_in_place_routine_witness :=
  @EvmAsm.Codegen.U256MulU64Be.mulWhole_inPlace_spec
private noncomputable abbrev _u256_div_u64_be_routine_witness :=
  @EvmAsm.Codegen.U256DivU64BeSAsm.u256DivU64BeInPlaceFlat_spec
-- #12461 arm 4: the two live K73 inhabitants and the five public composition
-- seams named in the row's notes.  The existing `_u256_mul_u64_be_routine_witness`
-- above is the already-landed callee anchor consumed by both inhabitants.
private noncomputable abbrev _k73_increase_entry_status_div_zero_clamp_witness :=
  @EvmAsm.Codegen.HeaderBaseFeeSpec.k73_increase_entry_status_div_zero_clamp_live_spec_within
private noncomputable abbrev _eip1559_calc_base_fee_per_gas_routine_witness :=
  @EvmAsm.Codegen.HeaderBaseFeeSpec.k73_increase_entry_status_div_zero_live_spec_within
private noncomputable abbrev _k73_increase_entry_to_mul_witness :=
  @EvmAsm.Codegen.HeaderBaseFeeSpec.k73_increase_entry_to_mul_spec_within
private noncomputable abbrev _k73_increase_status_div_zero_witness :=
  @EvmAsm.Codegen.HeaderBaseFeeSpec.k73_increase_status_div_zero_spec_within_for_return
private noncomputable abbrev _k73_increase_first_div_source_witness :=
  @EvmAsm.Codegen.HeaderBaseFeeSpec.k73_increase_first_div_source_branch_for_return
private noncomputable abbrev _k73_increase_second_add_witness :=
  @EvmAsm.Codegen.HeaderBaseFeeSpec.k73_increase_second_add_branch_for_return
private noncomputable abbrev _k73_increase_second_div_source_witness :=
  @EvmAsm.Codegen.HeaderBaseFeeSpec.k73_increase_second_div_source_branch_for_return
-- #12244 ask 3: first ambient-lift harvest.
private noncomputable abbrev _bnf_eq32_routine_witness :=
  @EvmAsm.Codegen.AmbientLifted.bnfEq32Flat_spec
-- The other three members of the same family, all instantiating `eqFamilyFlatSpec`.
private noncomputable abbrev _secf_eq32_routine_witness :=
  @EvmAsm.Codegen.AmbientLifted.secfEq32Flat_spec
private noncomputable abbrev _p256_eq32_routine_witness :=
  @EvmAsm.Codegen.AmbientLifted.p256Eq32Flat_spec
private noncomputable abbrev _blsg_eq48_routine_witness :=
  @EvmAsm.Codegen.AmbientLifted.blsgEq48Flat_spec
-- Ambient-FREE lift (`Fn.retSpecFlat`), four ABI args.
private noncomputable abbrev _call_frame_set_calldata_routine_witness :=
  @EvmAsm.Codegen.CallFrameCalldataFlat.callFrameSetCalldataFlat_spec
-- Ambient-FREE lift, read-only accessor geometry.
-- ⚠️ These two cite the PRE-EXISTING canonical lifts in their own Programs
-- modules, not the ambient-free proofs module. Duplicates of both were written
-- here and removed; the lifts had landed already (`de2fc7fe0`, `a9c898904`) and
-- the coincidence of names hid it, since the namespaces differ. Only the
-- non-vacuity proofs for them live in `AmbientFreeFlatTriples.lean`.
private noncomputable abbrev _secf_get_bit_lsb_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFlat_spec
private noncomputable abbrev _bah_u32le_routine_witness :=
  @EvmAsm.Codegen.BlockAccessListHashSAsm.bahU32leFlat_spec
-- ⚠️ `…FlatEntry_spec` again, NOT the `pdCr`-anchored twin.
private noncomputable abbrev _secf_is_zero32_routine_witness :=
  @EvmAsm.Codegen.AmbientFree.secfIsZero32FlatEntry_spec
-- ⚠️ `…FlatEntry_spec`, NOT the `pdCr`-anchored `secfZero32Flat_spec` in
-- `Secp256k1PointDoubleSAsmStage.lean`; see the row's notes.
private noncomputable abbrev _secf_zero32_routine_witness :=
  @EvmAsm.Codegen.AmbientFree.secfZero32FlatEntry_spec
-- ⚠️ THE OWN-MODULE one. Two other theorems share this name (`Bls12G2EncodeSAsm`
-- over `encCr`) or nearly (`Bls12KzgG2WireSAsm.blsgLeToBeWireFlat_spec` over
-- `wireCr`); neither is the image claim. See the row's notes.
private noncomputable abbrev _blsg_le_to_be_routine_witness :=
  @EvmAsm.Codegen.Bls12G1LeToBeSAsm.blsgLeToBeFlat_spec
-- ⚠️ Likewise the OWN-module one: `Bls12Fq12SetOneSAsm.blqZeroFlat_spec` shares this
-- name but is anchored over the `blqZero_prog ++ blqSetOne_prog` adjacency union.
-- ⚠️ Namespace is `Bls12Fq12Zero576SAsm`, which does NOT match its file name
-- (`Bls12Fq12ZeroSAsm.lean`).
private noncomputable abbrev _bnq_set_one_routine_witness :=
  @EvmAsm.Codegen.Bn254Fq12SetOneSAsm.bnqSetOneFrame_spec
private noncomputable abbrev _blsg2_copy192_routine_witness :=
  @EvmAsm.Codegen.Bls12G2Copy192SAsm.blsg2Copy192Frame_spec
private noncomputable abbrev _blq_set_one_routine_witness :=
  @EvmAsm.Codegen.Bls12Fq12SetOneSAsm.blqSetOneFrame_spec
private noncomputable abbrev _blq_zero_routine_witness :=
  @EvmAsm.Codegen.Bls12Fq12Zero576SAsm.blqZeroFlat_spec
-- Landed by #12380 (unrowed there); own-`CodeReq`, and no name collision this time.
private noncomputable abbrev _blsg_be_to_le_routine_witness :=
  @EvmAsm.Codegen.Bls12G1BeToLeSAsm.blsgBeToLeFlat_spec
-- ⚠️ `…FlatEntry_spec` again: the own-`CodeReq` primitive, NOT either of the two
-- caller-anchored `secfBeToLeFlat_spec` / `secfLeToBeFlat_spec` twins (`mulCr`,
-- `pdCr`), which are now corollaries of these.
private noncomputable abbrev _secf_be_to_le_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldConvSAsm.secfBeToLeFlatEntry_spec
private noncomputable abbrev _secf_le_to_be_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldConvSAsm.secfLeToBeFlatEntry_spec
-- Same shape, same warning, one curve over: the own-`CodeReq` primitives, NOT the
-- `addCr` / `mulCr` `bnfBeToLeFlat_spec` / `bnfLeToBeFlat_spec` twins that survive
-- in the two caller stage files as corollaries of these.
private noncomputable abbrev _bnf_be_to_le_routine_witness :=
  @EvmAsm.Codegen.Bn254FieldConvSAsm.bnfBeToLeFlatEntry_spec
private noncomputable abbrev _bnf_le_to_be_routine_witness :=
  @EvmAsm.Codegen.Bn254FieldConvSAsm.bnfLeToBeFlatEntry_spec
-- Flat all along behind `msetMemcpyBase` / `msetMemcpyCode`; the allowlist's
-- "anchored through some other base term" was about spelling, not the CodeReq.
private noncomputable abbrev _mset_memcpy_routine_witness :=
  @EvmAsm.Codegen.mset_memcpy_spec_within
-- The own-`CodeReq` entry triple, NOT the adjacency-anchored `bnqZeroFlat_spec`
-- of the same routine in `Bn254Fq12SetOneSAsm` (now a corollary of this).
private noncomputable abbrev _bnq_zero_routine_witness :=
  @EvmAsm.Codegen.Bn254Fq12ZeroSAsm.bnqZeroFlatEntry_spec
-- The frame-port four. Hand-built straight-line triples, no `Fn` involved — which
-- is why the allowlist's "needs Fn.retSpecFlat first" was false for all of them.
private noncomputable abbrev _frame_depth_push_routine_witness :=
  @EvmAsm.Codegen.FrameDepthPushSAsm.frameDepthPush_spec
private noncomputable abbrev _frame_depth_pop_routine_witness :=
  @EvmAsm.Codegen.FrameDepthPopSAsm.frameDepthPop_spec
private noncomputable abbrev _frame_save_regs_routine_witness :=
  @EvmAsm.Codegen.FrameSaveRegsSAsm.frameSaveRegs_spec
private noncomputable abbrev _frame_load_regs_routine_witness :=
  @EvmAsm.Codegen.FrameLoadRegsSAsm.frameLoadRegs_spec
-- The P-256 four. ⚠️ Each cites the `…Flat_spec` (or, for `p256_lt_be`, the flat
-- `_spec`), NOT the structured `…Fn_spec` its allowlist entry named.
private noncomputable abbrev _p256_be_to_le_routine_witness :=
  @EvmAsm.Codegen.P256BeToLeSAsm.p256BeToLeFlat_spec
private noncomputable abbrev _p256_le_to_be_routine_witness :=
  @EvmAsm.Codegen.P256LeToBeSAsm.p256LeToBeFlat_spec
private noncomputable abbrev _p256_copy_n_routine_witness :=
  @EvmAsm.Codegen.P256CopyNSAsm.p256CopyNFlat_spec
private noncomputable abbrev _p256_lt_be_routine_witness :=
  @EvmAsm.Codegen.P256LtBeSAsm.p256LtBe_spec
-- The BLS12 leaf eight. ⚠️ Namespace-qualified deliberately: `fq12IsZeroResult` and
-- `isZeroNResult` each exist twice in the tree under different curves.
private noncomputable abbrev _blq_copy_routine_witness :=
  @EvmAsm.Codegen.Bls12Fq12CopySAsm.blqCopyFlat_spec
private noncomputable abbrev _blq_pt_copy_routine_witness :=
  @EvmAsm.Codegen.Bls12PtCopySAsm.blqPtCopyFlat_spec
private noncomputable abbrev _blsg_copy96_routine_witness :=
  @EvmAsm.Codegen.Bls12G1Copy96SAsm.blsgCopy96Flat_spec
private noncomputable abbrev _blsf_copy_quads_routine_witness :=
  @EvmAsm.Codegen.Bls12FieldCopyQuadsSAsm.blsfCopyQuadsFlat_spec
private noncomputable abbrev _blsg_zero96_routine_witness :=
  @EvmAsm.Codegen.Bls12G1Zero96SAsm.blsgZero96Flat_spec
private noncomputable abbrev _blsg2_zero192_routine_witness :=
  @EvmAsm.Codegen.Bls12G2Zero192SAsm.blsg2Zero192Flat_spec
private noncomputable abbrev _blq_is_zero_routine_witness :=
  @EvmAsm.Codegen.Bls12Fq12IsZeroSAsm.blqIsZeroFlat_spec
private noncomputable abbrev _blsg_is_zero_n_routine_witness :=
  @EvmAsm.Codegen.Bls12G1IsZeroNSAsm.blsgIsZeroNFlat_spec
-- The final nine. ⚠️ Namespaces matter more than usual here: `ltPBase` resolves to
-- four different guest addresses across the tree and `leU64` exists three times.
private noncomputable abbrev _bgv_u64le_routine_witness :=
  @EvmAsm.Codegen.BalGasValidU64SAsm.bgvU64leFlat_spec
private noncomputable abbrev _blk2_ld_le64_routine_witness :=
  @EvmAsm.Codegen.Blake2fLoadLe64SAsm.blk2LdLe64Flat_spec
private noncomputable abbrev _blk2_st_le64_routine_witness :=
  @EvmAsm.Codegen.Blake2fStoreLe64SAsm.blk2StLe64Flat_spec
private noncomputable abbrev _bloom_or_into_routine_witness :=
  @EvmAsm.Codegen.BloomOrIntoSAsm.bloomOrIntoFlat_spec
private noncomputable abbrev _blsk_lt_be_routine_witness :=
  @EvmAsm.Codegen.Bls12KzgLtBeSAsm.blskLtBe_spec
private noncomputable abbrev _bn254_call_allotment_routine_witness :=
  @EvmAsm.Codegen.Bn254CallAllotmentSAsm.bn254CallAllotment_spec
private noncomputable abbrev _dispatcher_capture_exec_state_gas_routine_witness :=
  @EvmAsm.Codegen.DispatcherCaptureExecStateGasSAsm.dispatcherCaptureExecStateGas_spec
private noncomputable abbrev _hp_encode_nibbles_routine_witness :=
  @EvmAsm.Codegen.HpEncodeNibblesSAsm.hpEncodeNibblesFlat_spec
private noncomputable abbrev _mpt_resolve_cache_reset_routine_witness :=
  @EvmAsm.Codegen.MptResolveCacheResetSAsm.mptResolveCacheReset_spec
-- The three composite callers. ⚠️ These witnesses are anchored over UNION CodeReqs on
-- purpose: each routine calls its callee, so the union is required, and every
-- component was checked against `GuestImageEntries` before rowing.
private noncomputable abbrev _blsg2_encode_routine_witness :=
  @EvmAsm.Codegen.Bls12G2EncodeSAsm.blsg2Encode_spec
private noncomputable abbrev _blsk_g2_wire_routine_witness :=
  @EvmAsm.Codegen.Bls12KzgG2WireSAsm.blskG2Wire_spec
private noncomputable abbrev _bnf_add_mod_p_routine_witness :=
  @EvmAsm.Codegen.Bn254FieldAddModPSAsm.bnfAddModP_spec
-- The two MUL twins. ⚠️ Their `mulCr`s are DIFFERENT CodeReqs sharing a name across
-- three modules; the namespaces below are what disambiguates them.
private noncomputable abbrev _bnf_mul_mod_p_routine_witness :=
  @EvmAsm.Codegen.Bn254FieldMulModPSAsm.bnfMulModP_spec
private noncomputable abbrev _secf_mul_mod_p_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldMulModPSAsm.secfMulModP_spec
-- The two witness-index entry triples. ⚠️ `…Entry_spec`, NOT the position-independent
-- `widx_*_spec` they are instantiated from — those are at a free base and are not the
-- image claim.
private noncomputable abbrev _widx_cmp32_routine_witness :=
  @EvmAsm.Codegen.Proofs.widxCmp32Entry_spec
private noncomputable abbrev _wcidx_cmp32_routine_witness :=
  @EvmAsm.Codegen.Proofs.wcidxCmp32Entry_spec
private noncomputable abbrev _widx_record_ptr_routine_witness :=
  @EvmAsm.Codegen.Proofs.widxRecordPtrEntry_spec
-- The first `model-only` lift. ⚠️ Cites the FLAT `…Flat_spec`, not the structured
-- `bncZero64Fn_spec` it is derived from.
private noncomputable abbrev _bnc_zero64_routine_witness :=
  @EvmAsm.Codegen.Bn254CurveZeroSAsm.bncZero64Flat_spec
private noncomputable abbrev _secp256k1_point_zero64_routine_witness :=
  @EvmAsm.Codegen.Secp256k1PointZero64SAsm.secp256k1PointZero64Flat_spec
private noncomputable abbrev _bnp_fp2_zero_routine_witness :=
  @EvmAsm.Codegen.Bn254Fp2ZeroSAsm.bnpFp2ZeroFlat_spec
private noncomputable abbrev _bnc_copy64_routine_witness :=
  @EvmAsm.Codegen.Bn254CurveCopySAsm.bncCopy64Flat_spec
private noncomputable abbrev _secp256k1_point_double_routine_witness :=
  @EvmAsm.Codegen.Secp256k1PointDoubleSAsm.pointDouble_spec
-- #12319 review follow-up: the row's note asserts the `SpecRef.pointAdd` bridge
-- is discharged, and a claim in a note that no gate checks is exactly the blind
-- spot the comment at the row itself records.  So the bridge theorem is
-- registered as an ADDITIONAL witness here, in the same
-- `k73_increase_*`-style "seam named in the row's notes" pattern used above.
-- ⚠️ Registered ALONGSIDE rather than REPLACING the original, for two reasons
-- that both come from name-sensitivity:
--   * `gen-axiom-witnesses.py`'s `check_refs` matches a row's `some "…"` ref by
--     DOTTED SUFFIX against the abbrev targets, and
--     `…SAsm.pointDouble_spec_pointAdd` does NOT end in `.pointDouble_spec`, so
--     retargeting this abbrev alone would orphan the row's ref;
--   * `check-registry-coverage` maps a witness by stripping `_spec`, and
--     `pointDouble_spec_pointAdd` has no `_spec` SUFFIX to strip -- it would
--     reintroduce the very census blind spot documented at this row.
-- Both theorems are the SAME triple (12 hypotheses each, identical step bound,
-- entry/exit, `pdCr` and footprint); the bridge's post is strictly more
-- informative, so covering both costs one extra `#print axioms` line.
private noncomputable abbrev _secp256k1_point_double_pointadd_bridge_witness :=
  @EvmAsm.Codegen.Secp256k1PointDoubleSAsm.pointDouble_spec_pointAdd
private noncomputable abbrev _secp256k1_point_copy64_routine_witness :=
  @EvmAsm.Codegen.Secp256k1PointCopy64SAsm.secp256k1PointCopy64Flat_spec
private noncomputable abbrev _bnp_fp2_copy_routine_witness :=
  @EvmAsm.Codegen.Bn254Fp2CopySAsm.bnpFp2CopyFlat_spec
private noncomputable abbrev _bnq_copy_routine_witness :=
  @EvmAsm.Codegen.Bn254Fq12CopySAsm.bnqCopyFlat_spec
private noncomputable abbrev _bnq_pt_copy_routine_witness :=
  @EvmAsm.Codegen.Bn254PtCopySAsm.bnqPtCopyFlat_spec
-- ⚠️ Namespace-qualified: `fq12IsZeroResult` exists for both curves at different widths.
private noncomputable abbrev _bnq_is_zero_routine_witness :=
  @EvmAsm.Codegen.Bn254Fq12IsZeroSAsm.bnqIsZeroFlat_spec
private noncomputable abbrev _bnp_fp2_is_zero_routine_witness :=
  @EvmAsm.Codegen.Bn254Fp2IsZeroSAsm.bnpFp2IsZeroFlat_spec
-- ⚠️ In `AmbientFree`, not `Bn254Field` — the lift sits beside its secf template.
private noncomputable abbrev _bnf_is_zero32_routine_witness :=
  @EvmAsm.Codegen.AmbientFree.bnfIsZero32FlatEntry_spec
private noncomputable abbrev _bnc_is_inf64_routine_witness :=
  @EvmAsm.Codegen.AmbientFree.bncIsInf64FlatEntry_spec
private noncomputable abbrev _enrg_u32le_routine_witness :=
  @EvmAsm.Codegen.Eip7702NonceReuseGuardSAsm.enrgU32leFlat_spec
-- #12244 ask 3: needed no lift; the flat triple already existed.
private noncomputable abbrev _secf_reduce_once_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldReduceOnceSAsm.secfReduceOnceFrame_spec
private noncomputable abbrev _secf_reduce_once_n_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldReduceOnceNSAsm.secfReduceOnceNFrame_spec
private noncomputable abbrev _secf_copy32_routine_witness :=
  @EvmAsm.Codegen.Secp256k1FieldReduceOnceSAsm.secfCopy32Direct_spec
-- #12245 flat-block pilot: eight machine-level strongest-post contracts.
private noncomputable abbrev _wcidx_record_ptr_routine_witness :=
  @EvmAsm.Codegen.Proofs.wcidxRecordPtrFlat_spec
private noncomputable abbrev _write_sets_discard_tx_routine_witness :=
  @EvmAsm.Codegen.Proofs.writeSetsDiscardTxFlat_spec
private noncomputable abbrev _read_sets_discard_tx_routine_witness :=
  @EvmAsm.Codegen.Proofs.readSetsDiscardTxFlat_spec
private noncomputable abbrev _secf_square_mod_p_routine_witness :=
  @EvmAsm.Codegen.Proofs.secfSquareModPFlat_spec
private noncomputable abbrev _secf_square_mod_n_routine_witness :=
  @EvmAsm.Codegen.Proofs.secfSquareModNFlat_spec
private noncomputable abbrev _rlp_walk_next_core_routine_witness :=
  @EvmAsm.Rv64.RLP.rlp_walk_next_spec_within
private noncomputable abbrev _derive_withdrawal_requests_routine_witness :=
  @EvmAsm.Codegen.Proofs.deriveWithdrawalRequestsFlat_spec
private noncomputable abbrev _derive_consolidation_requests_routine_witness :=
  @EvmAsm.Codegen.Proofs.deriveConsolidationRequestsFlat_spec
-- #12226 harvest: seven flat triples the `_spec_within`/`Flat_spec` suffix
-- heuristic graded tier B. Unwitnessed by `check-axioms.sh` until now.
private noncomputable abbrev _bloom_eq_routine_witness :=
  @EvmAsm.Codegen.BloomEqSAsm.bloomEq_spec
private noncomputable abbrev _blq_eq_routine_witness :=
  @EvmAsm.Codegen.Bls12Fq12EqSAsm.blqEq_spec
private noncomputable abbrev _bnq_eq_routine_witness :=
  @EvmAsm.Codegen.Bn254Fq12EqSAsm.bnqEq_spec
private noncomputable abbrev _bnp_fp2_eq_routine_witness :=
  @EvmAsm.Codegen.Bn254Fp2EqSAsm.bnpFp2Eq_spec
private noncomputable abbrev _blsg2_eq_n_routine_witness :=
  @EvmAsm.Codegen.Bls12G2EqNSAsm.blsg2EqN_spec
private noncomputable abbrev _frame_base_routine_witness :=
  @EvmAsm.Codegen.CallFrameBaseSAsm.frameBase_spec
private noncomputable abbrev _u256_min_routine_witness :=
  @EvmAsm.Codegen.U256MinSAsm.u256Min_spec
-- #12659 Stage 2: the linked priority body and gas-result entry witnesses.
private noncomputable abbrev _priority_fee_per_gas_eip1559_body_routine_witness :=
  @EvmAsm.Codegen.U256GasPricingSAsm.priority_fee_per_gas_eip1559_body_spec
private noncomputable abbrev _tx_gas_result_increments_routine_witness :=
  @EvmAsm.Codegen.TxGasResultIncrementsSAsm.tx_gas_result_increments_spec
private noncomputable abbrev _blsg_lt_p_routine_witness :=
  @EvmAsm.Codegen.Bls12G1LtPSAsm.blsgLtP_spec
private noncomputable abbrev _blsg_lt_p_specref_routine_witness :=
  @EvmAsm.Codegen.blsgLtP_spec_specref
private noncomputable abbrev _bnf_lt_p_routine_witness :=
  @EvmAsm.Codegen.Bn254FieldLtPSAsm.bnfLtP_spec
private noncomputable abbrev _bnf_lt_p_specref_routine_witness :=
  @EvmAsm.Codegen.bnfLtP_spec_specref
-- #11925 last-of-six: the whole-routine triple lives in the `TxTypeDispatchTop`
-- module, in the `…TxTypeDispatchSpec` namespace.
private noncomputable abbrev _tx_type_dispatch_routine_witness :=
  @EvmAsm.Codegen.TxTypeDispatchSpec.txTypeDispatch_spec_within
-- #11800 follow-on: zkvm_keccak256 whole-routine wrapper over #11960 framing.
private noncomputable abbrev _zkvm_keccak256_routine_witness :=
  @EvmAsm.Codegen.Proofs.zkvm_keccak256_spec_within
private noncomputable abbrev _block_hash_from_header_routine_witness :=
  @EvmAsm.Codegen.BlockHashFromHeaderSpec.block_hash_from_header_spec_within
-- #12223 close-out: the same routine against `SpecRef.headerHash`, plus the two
-- legs it composes. Witnessed separately because the row carries one `spec`
-- string and these are the claims its notes cite by name.
private noncomputable abbrev _block_hash_from_header_headerHash_witness :=
  @EvmAsm.Codegen.BlockHashFromHeaderSpec.block_hash_from_header_headerHash_within
private noncomputable abbrev _block_hash_from_header_hash_leg_witness :=
  @EvmAsm.Codegen.BlockHashFromHeaderSpec.keccakBodyDigest_encode_eq_headerHash
private noncomputable abbrev _block_hash_from_header_seam_witness :=
  @EvmAsm.Codegen.BlockHashFromHeaderSpec.keccakBodyDigest_eq_headerHash_of_decode
private noncomputable abbrev _header_rlp_round_trip_witness :=
  @EvmAsm.Stateless.SpecRef.encode_headerToRlpItem_of_decode
-- #12318: the second six-instruction keccak wrapper, at its own linked base.
-- The two non-vacuity terms are forced here as well, so the axiom gate audits
-- the satisfying instance and its negative control, not only the triple.
private noncomputable abbrev _block_access_list_hash_core_routine_witness :=
  @EvmAsm.Codegen.BlockAccessListHashCoreSpec.block_access_list_hash_core_spec_within
private noncomputable abbrev _block_access_list_hash_core_reachable_witness :=
  @EvmAsm.Codegen.BlockAccessListHashCoreSpec.blockAccessListHashCore_precondition_reachable
private noncomputable abbrev _block_access_list_hash_core_control_witness :=
  @EvmAsm.Codegen.BlockAccessListHashCoreSpec.blockAccessListHashCore_precondition_negative_control
private noncomputable abbrev _address_from_pubkey_routine_witness :=
  @EvmAsm.Codegen.AddressFromPubkeySpec.addressFromPubkey_spec_within
private noncomputable abbrev _blockhash_from_witness_headers_routine_witness :=
  @EvmAsm.Codegen.BlockHashFromWitnessHeadersSpec.blockhash_from_witness_headers_spec_within_empty_section
-- #12037: pure operational digest → SpecRef.keccak256 (load-bearing for #12038).
private noncomputable abbrev _keccakBodyDigest_eq_specref_witness :=
  @EvmAsm.Codegen.Proofs.keccakBodyDigest_eq_specref
-- #12108: the segments gather entry point; `_sample_witness` is the compiled
-- satisfying instance, forced here so the axiom gate sees the non-vacuity term
-- and not only the theorem it instantiates. Multi-rate (ungated) triple.
private noncomputable abbrev _zkvm_keccak256_segments_routine_witness :=
  @EvmAsm.Codegen.Proofs.zkvm_keccak256_segments_spec_within
private noncomputable abbrev _zkvm_keccak256_segments_sample_witness :=
  @EvmAsm.Codegen.Proofs.kss_sample_witness_multi
private noncomputable abbrev _zkvm_keccak256_segments_digest_bridge_witness :=
  @EvmAsm.Codegen.Proofs.kssDigest_eq_specref_any
private noncomputable abbrev _keccakBodyDigest_div_eq_specref_witness :=
  @EvmAsm.Codegen.Proofs.keccakBodyDigest_div_eq_specref
-- #12018: SHA-256 whole-routine triple (closes the phase witnesses below).
private noncomputable abbrev _zkvm_sha256_routine_witness :=
  @EvmAsm.Codegen.Proofs.zkvm_sha256_spec_within
-- #12018 phase witnesses retained: frame/setup/prefix/loop boundaries that
-- the top triple composes over.
private noncomputable abbrev _zkvm_sha256_frame_witness :=
  @EvmAsm.Codegen.Proofs.sha256Frame_spec
private noncomputable abbrev _zkvm_sha256_setup_witness :=
  @EvmAsm.Codegen.Proofs.sha256SetupMoves_spec
private noncomputable abbrev _zkvm_sha256_full_block_prefix_witness :=
  @EvmAsm.Codegen.Proofs.sha256FullBlockPrefix_spec
private noncomputable abbrev _zkvm_sha256_full_block_loop_witness :=
  @EvmAsm.Codegen.Proofs.sha256FullBlockLoop_reload_spec
-- #11578 rescope: execution_requests_hash validation-accept prefix.
private noncomputable abbrev _execution_requests_hash_routine_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashWrap.execution_requests_hash_validation_accept
-- #12011 hash-half: erh_hash_one empty+nonempty tops under residual h_sha.
-- No Routines ROW yet (whole erh/rhv still open); witnesses still required so
-- check-axioms covers these modules (same pattern as #12018 phase witnesses).
private noncomputable abbrev _erh_hash_one_empty_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashHashOneTop.erh_hash_one_spec_within_empty
private noncomputable abbrev _erh_hash_one_nonempty_witness :=
  @EvmAsm.Codegen.ExecutionRequestsHashHashOneNonemptyTop.erh_hash_one_spec_within_nonempty
-- #12206: `assemble_execution_requests` whole routine (imported above —
-- `EvmAsm.Codegen.Programs.AssembleExecutionRequestsTop`).
private noncomputable abbrev _assemble_execution_requests_routine_witness :=
  @EvmAsm.Codegen.AssembleExecutionRequestsTop.assemble_execution_requests_spec_within
-- #12206 item 2: `requests_hash_verify` whole routine (imported above). The
-- non-vacuity instance and BOTH kinds of negative control get witnesses too, so
-- the axiom gate audits the satisfiability evidence and not only the triple.
private noncomputable abbrev _requests_hash_verify_routine_witness :=
  @EvmAsm.Codegen.RequestsHashVerifyTop.requests_hash_verify_spec_within
private noncomputable abbrev _requests_hash_verify_gate_reachable_witness :=
  @EvmAsm.Codegen.RequestsHashVerifyTop.rhv_gate_reachable
private noncomputable abbrev _requests_hash_verify_residual_reachable_witness :=
  @EvmAsm.Codegen.RequestsHashVerifyTop.rhv_residual_reachable
private noncomputable abbrev _requests_hash_verify_gate_unaligned_witness :=
  @EvmAsm.Codegen.RequestsHashVerifyTop.rhv_gate_unaligned
private noncomputable abbrev _requests_hash_verify_gate_short_witness :=
  @EvmAsm.Codegen.RequestsHashVerifyTop.rhv_gate_short_expected
private noncomputable abbrev _requests_hash_verify_residual_wrong_site_witness :=
  @EvmAsm.Codegen.RequestsHashVerifyTop.rhv_residual_wrong_site
private noncomputable abbrev _requests_hash_verify_rhv_hash_gate_witness :=
  @EvmAsm.Codegen.RequestsHashVerifyTop.rhvHash_gate
-- #12038 / #12324: K145 `tx_signing_hash` short-domain whole-routine triple.
private noncomputable abbrev _tx_signing_hash_routine_witness :=
  @EvmAsm.Codegen.TxSigningHashSpec.tx_signing_hash_spec_within
-- #12038: K147 EIP-7702 authorization signing hash, whole routine, under the
-- named unproven-callee residual for K145 `tx_signing_hash`.
private noncomputable abbrev _eip7702_authorization_signing_hash_routine_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.eip7702_authorization_signing_hash_spec_within
-- The SpecRef tie (by `rfl`): the digest IS `recover_authority`'s `signing_hash`.
private noncomputable abbrev _eip7702_auth_signing_hash_specref_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.recover_authority_unfold
-- Structural drift guard on the emitted routine + its cross-`jal` reloc.
private noncomputable abbrev _eip7702_auth_signing_hash_frame_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.eip7702AuthorizationSigningHash_prog_eq_frame
private noncomputable abbrev _eip7702_auth_signing_hash_jal_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.authJal_target
-- coverRef: the residual's computable half, discharged at the real call site.
private noncomputable abbrev _eip7702_auth_signing_hash_cover_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.authCallSite_ok_sample
-- Field-position pinning (general short-list form + the concrete 25 bytes).
private noncomputable abbrev _eip7702_auth_signing_hash_segments_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.authSigningPreimage_segments
private noncomputable abbrev _eip7702_auth_signing_hash_preimage_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.sampleAuth_preimage
private noncomputable abbrev _eip7702_auth_signing_hash_decodes_witness :=
  @EvmAsm.Codegen.Eip7702AuthSigningHashSpec.sampleAuth_decodes
-- #11800 node-DB half: whole-routine `node_db_lookup` triple, its compiled
-- non-vacuity instance, and the composition to `SpecRef.build_node_db`.
private noncomputable abbrev _node_db_lookup_routine_witness :=
  @EvmAsm.Codegen.NodeDbLookupSpec.node_db_lookup_spec_within
private noncomputable abbrev _node_db_lookup_sample_witness :=
  @EvmAsm.Codegen.NodeDbLookupSpec.node_db_lookup_sample_witness
private noncomputable abbrev _node_db_lookup_specref_witness :=
  @EvmAsm.Codegen.NodeDbLookupSpec.node_db_lookup_result_eq_build_node_db
-- #12036/#12144/#12183: production enable=1 empty top + three-site residual.
-- Blocker 1 retired; walk fullCode unions indexed for enableFull ⊆ walk.
private noncomputable abbrev _witness_lookup_by_hash_routine_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.witness_lookup_by_hash_spec_within_enabled_empty
-- #12036: enable=1 HIT arm whole-routine top (widx_count = 1, coverHit) and
-- the generalized indexed callee it composes (scratch temps symbolic, so the
-- parent's `x6 = wlh_indexed_calls + 1` and `x11 = a1` can be instantiated).
private noncomputable abbrev _witness_lookup_by_hash_enabled_one_hit_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.witness_lookup_by_hash_spec_within_enabled_one_hit
private noncomputable abbrev _witness_lookup_by_hash_indexed_one_hit_gen_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit.witness_lookup_by_hash_indexed_spec_within_one_hit_gen
private noncomputable abbrev _witness_lookup_by_hash_hit_cells_distinct_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.hit_cells_distinct
private noncomputable abbrev _witness_lookup_by_hash_legacy_empty_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.witness_lookup_by_hash_spec_within_empty_section
private noncomputable abbrev _witness_lookup_by_hash_sample_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_empty_section_sample_witness
private noncomputable abbrev _witness_lookup_by_hash_frame_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_abiFrame_byte_tie
private noncomputable abbrev _witness_lookup_by_hash_callwithin_en_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlhCallWithin_enabled_empty
private noncomputable abbrev _witness_lookup_by_hash_callwithin_legacy_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlhCallWithin_empty_section
private noncomputable abbrev _witness_lookup_by_hash_entry_in_fullcode_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_entry_in_walk_fullCode
private noncomputable abbrev _witness_lookup_by_hash_gap_cells_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlh_cells_outside_residual_footprint
private noncomputable abbrev _wl_enabled_empty_root_witness :=
  @EvmAsm.Codegen.MptWalkSpec.root_wl_enabled_empty_establishes_shape
private noncomputable abbrev _wl_enabled_empty_branch_witness :=
  @EvmAsm.Codegen.MptWalkSpec.branch_wl_enabled_empty_establishes_shape
private noncomputable abbrev _wl_enabled_empty_ext_witness :=
  @EvmAsm.Codegen.MptWalkSpec.ext_wl_enabled_empty_establishes_shape
-- #12036: enable=1 HIT residual at `widx_count = 1`, three-site discharge
-- (`wlCallWithinShapeHitEn`), plus its satisfiability + negative control.
private noncomputable abbrev _witness_lookup_by_hash_callwithin_hit_witness :=
  @EvmAsm.Codegen.WitnessLookupByHashSpec.wlhCallWithin_enabled_one_hit
private noncomputable abbrev _wl_enabled_hit_root_witness :=
  @EvmAsm.Codegen.MptWalkSpec.root_wl_enabled_hit_establishes_shape
private noncomputable abbrev _wl_enabled_hit_branch_witness :=
  @EvmAsm.Codegen.MptWalkSpec.branch_wl_enabled_hit_establishes_shape
private noncomputable abbrev _wl_enabled_hit_ext_witness :=
  @EvmAsm.Codegen.MptWalkSpec.ext_wl_enabled_hit_establishes_shape
private noncomputable abbrev _wl_enabled_hit_sat_witness :=
  @EvmAsm.Codegen.MptWalkSpec.root_wl_enabled_hit_shape_sat
private noncomputable abbrev _wl_enabled_hit_negctl_witness :=
  @EvmAsm.Codegen.MptWalkSpec.root_wl_enabled_hit_shape_wrong_offset_false
private noncomputable abbrev _wl_enabled_hit_model_witness :=
  @EvmAsm.Codegen.MptWalkWlEnabledHitSat.hit_site_entryState_exists
private noncomputable abbrev _wl_enabled_hit_model_shape_witness :=
  @EvmAsm.Codegen.MptWalkWlEnabledHitSat.sample_site_shape
-- #12244: one base-parameterized lift, two guest addresses.
private noncomputable abbrev _swr_rev_le_be_routine_witness :=
  @EvmAsm.Codegen.RevLeBeFlat.swrRevLeBeFlat_spec
private noncomputable abbrev _bhr_rev_le_be_routine_witness :=
  @EvmAsm.Codegen.RevLeBeFlat.bhrRevLeBeFlat_spec
-- #12244: three u32le wrappers pinned via bah's twin; shared sgLoadU32leFn untouched.
private noncomputable abbrev _spw_u32le_routine_witness :=
  @EvmAsm.Codegen.SszPayloadWithdrawalsSAsm.spwU32leFlat_spec
private noncomputable abbrev _sws_u32le_routine_witness :=
  @EvmAsm.Codegen.SszWitnessStateSAsm.swsU32leFlat_spec
-- #12318: the x29-preserving companion frame for `sws_u32le`. Separate row,
-- separate witness; the sibling above is untouched.
private noncomputable abbrev _sws_u32le_pres_routine_witness :=
  @EvmAsm.Codegen.SszWitnessStateSectionSpec.swsU32lePresFlat_spec
private noncomputable abbrev _eph_u32le_routine_witness :=
  @EvmAsm.Codegen.EphU32leSAsm.ephU32leFlat_spec
private noncomputable abbrev _ssz_pack_bytes_routine_witness :=
  @EvmAsm.Codegen.SszPackBytesSAsm.sszPackBytesFlat_spec
private noncomputable abbrev _p256_is_zero_n_routine_witness :=
  @EvmAsm.Codegen.P256IsZeroNSAsm.p256IsZeroNFlat_spec
-- #12222: the BAL read-half producer's suppressed arm.
private noncomputable abbrev _account_read_record_routine_witness :=
  @EvmAsm.Codegen.Proofs.accountReadRecordSuppressedFlat_spec

end EvmAsm.Progress
