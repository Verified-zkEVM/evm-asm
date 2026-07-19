/-
  Composition scaffolding for unconditional `block_verdict_tx_state_gas_array`.

  Status (a4gbr track):
  * Array tops (#10432+#10437+#10442): conditional on
    IntrinsicAssumed / TeerAssumed / BgvOffsetAssumed (named hyps).
  * Intrinsic leaf (#10434): framed success under ExtractAssumed +
    TypeDispatchAssumed; ets proven.
  * Discharge (`TxIntrinsicStateGasDischarge`): framed → IntrinsicAssumed
    shape at **off = 0, len = bs.length** (slice-eq-ambient), still under
    TisCalleeAssumptions. **regOwn temp peel DONE**
    (`intrinsicAssumed_success_flat_off0_own`); multi-tx ambient residual.
  * Teer leaf (prover1): targets TeerAssumed.applied_flat verbatim; body
    modulo input callees; will ping when top lands.
  * prior_exact (#10433): success + mid-loop overflow complete (gate sum).
  * **BgvOffsetAssumed DISCHARGED** (`bgvOffsetAssumed_fullCode`): ambient
    LBU compose for unaligned loop-site `bgv_u32le` (classical-3).
  * **TypeDispatchAssumed DISCHARGED** (`typeDispatchAssumed_fullCode`):
    success-domain leaf + memOwn/regOwn peel under fullCode (classical-3).

  Residual set for "unconditional" a4gbr claim (honest):
  1. TeerAssumed ← prover1 teer top (modulo remaining input callees)
  2. IntrinsicAssumed ← multi-tx ambient (off ≠ 0): TypeDispatch ambient
     Assumed DONE (`typeDispatchAssumedAmbient_fullCode`); residual
     ExtractAssumed ambient + Intrinsic off≠0 discharge
   3. TisCalleeAssumptions ← ExtractAssumed: **Program convert DONE** +
       **stack honesty DONE** (`ExtractAssumed` pins `x2`+`stackFree 10`;
       `nIntrinsicStackDwords` 8→18; discharge `stackFree18_split`).
       **toBuf/tea honesty DONE** (`extractToBufOwn` 3 dwords + `teaScratchOwn`;
       `tisScratchOwn` 8 cells). Packaging substrate + extractSuccess domain.
        **Frame save/restore DONE** + **pre-zero DONE** (`extractPreZero` E+56→E+72) +
        **type_dispatch call DONE** (`extractTypeSuccess` E+72→E+112, value-carrying
        tea post) + **load type/inner DONE** (`extractLoadTypeInner` E+112→E+144) +
        **walk_init DONE** (`extractWalkInitCall`+BNE E+144→E+152) +
        **save cursor + first walk_next skip DONE** (`extractSaveCursor` E+152→E+160;
        `extractWalkNext0Call`+BNE E+184→E+192 under extractLinkedCode).
        **type-branch DONE** (`extractTypeBranchLegacy/T1/Type234`).
        **all type walk chains DONE**; **HaveField both exits DONE**
        (`extractHaveFieldCreation` + `extractHaveFieldCopy` → EpiRestore
         classical-3). **walk_init 9-way→OkFail DONE** + **OK exists_pre
         bneSave DONE** + **s5/s6 frame through call DONE** + **type234
         AfterSave→WalkNext0 framed DONE** (`extractType234ToWalkNext0`).
         **wn0 call_type234 + OkFail DONE** (`extractWalkNext0Call_type234`) +
         **wn0 OK exists_pre→BNE DONE** (`extractWalkNext0OkNested_bne`).
         **wn1..5 ambient DONE** (`TopWalkNext1` + `TopWalkNextRest`).
         **legacy ambient DONE** (`TopLegacy` walk0..3 + ToHaveField).
         **t1 ambient DONE** (`TopT1` walk0..4 + ToHaveField).
         **type234 HaveField join ambient DONE**; **HaveField creation/copy
         framed DONE** (`TopHaveField` → EpiRestore).
          **epilogue linked+framed DONE** (`extractEpilogueSuccess_framed`).
          **stack frame ambient DONE** + **frameSlotsSaved_imp_stackFree10 DONE**
          + **both HaveField exits→epi DONE**
          (`extractHaveFieldCreation_then_epi` + `extractHaveFieldCopy_then_epi`).
           **midOwned through type234+legacy+t1 walks + type-branch DONE**;
           **all three HaveField→epi under midOwned DONE**
           (type234/legacy/t1 creation+copy → ret with stackFree10).
           **type234 mid-seq PrepCallOk wn0..wn5 DONE** (`TopMidSeq` +
           `TopMidSeqRest`; a2-any closes prep→call gap; hok drop-fail residual).
           **type234 chain AfterSave→wn0..wn5 Ok DONE** (`TopMidChain` +
           `TopMidChainRest`) + **AfterSave→creation→ret DONE**
           (`extractType234AfterSaveCreation_then_epi`) +
           **AfterSave→20B copy→ret DONE**
           (`extractType234AfterSaveCopy_then_epi`; contentDwords +
           hlen20/hnext_content residual).
           **front→WalkInitJalPc DONE** (`extractFrontThenTypeLoad`;
           model pure extractSuccess_outcome/creation/copy).
           **front E→AfterSave DONE** (`extractFrontToAfterSave` + drop-fail);
           **frontAfterSave→midJoinPre bridge DONE** (`frontAfterSave_to_midJoinPre`).
           **front AfterSave→creation→ret DONE** (`extractFrontAfterSaveCreation_then_epi`);
           **front AfterSave→copy→ret DONE** (`extractFrontAfterSaveCopy_then_epi`);
           **E→ret type234 creation DONE** (`extractFrontCreation_then_epi`);
           **E→ret type234 copy DONE** (`extractFrontCopy_then_epi`).
           **nExtractSteps 512→1024** (covers E2E ≈949/956) + **nIntrinsicSteps
           1024→1536** (covers nTisTopSteps ≈1333); mono lemmas
           `nFrontCreation_le_nExtract` / `nFrontCopy_le_nExtract`.
           **callee-saved s0–s7 pin DONE** (`ExtractAssumed` + `IntrinsicAssumed`
           pin x8,x9,x18–x23; array x23=endW concrete; loopIntrinsicFrame drops x23).
            **creationPost_to_assumed DONE** (KEEP s-regs; memIs→memOwn isCre/tea;
            regIs→regOwn temps; classical-3).
            **assumedPreConcrete_to_e2e DONE** (stackFree10_eq_frameSlotsOwn).
            **extractAssumed_creation_temps DONE** (of_forall6 peels x5/x6/x7/x14–16;
            mono nFrontCreation→nExtract; Assumed pre/post under extractLinkedCode
            given hE2E for all old temps).
            **extractAssumed_creation_under_honesty / _fullCode DONE** (wire
            FrontCreation E2E → Assumed shape under extractLinkedCode/fullCode;
            still takes honesty residuals hdrop/hok*/hnext*/hcre + walk statics).
            **pure honesty substrate DONE** (`extractSuccess_inner_lt` = walk_init
            hoff; `toFieldIndex_*` / type234 index; `creation_to_empty` /
            `copy_to_len20`; `rlpItemDecode_empty_short` / `_addr20_short` +
            `rlpWalkNextOk_empty_short`; `decodeListItems_eq_encode` +
            `decodeListItems_short_walkInit_guards` + `extractSuccess_inner_eq_encode`
            for short-list walk_init pure guards;
            `extractSuccess_short_walkInit_guards` Word-level short success pure
            under extractSuccess + hshort ≤55;
             `extractWalkInitCall_short` + `extractWalkInitShortPost_to_okNested`
             short leaf call under extractLinkedCode, a2=0 OK nested post;
             **short Front→AfterSave DONE** (`extractWalkInitCall_short_fromTypeLoad`
             + `_ok_framed_s5s6` + `extractFrontToAfterSave_short` — no universal
             walkInitOkFail_drop; short pure hyps only).
             **concrete short AfterSave DONE** (`ShortOkRegs`, `frontAfterSavePostShort`,
             `extractWalkInitCall_short_toAfterSave_concrete` — cursor/end pinned).
              Decode-gated hcre + hlen20 + hnext_content DONE
              (`wn5OkConcrete` keeps `rlpItemDecode`; hcre/hlen20/hnext_content
              are decode-gated via pfx80/pfx94; pure
              `hnext_content_decode_of_pfx94` when contentPtr=cursor+1).
              **Honest hok path DONE wn0..wn5**: `wn0Outcome_drop_fail_of_decode`
              + `*CallOk/*PrepCallOk_owned_of_decode` (Outcome post).
              **MidChain of_decode DONE** (`TopMidChainDecode` ToWn5).
              **MidJoin+Front AfterSave of_decode DONE** (creation+copy;
              hdec+hinb ∀endPtr). **FrontE2E of_decode DONE** (E→ret creation;
              no hok*). **E2ECopy of_decode DONE**. **Assumed creation short+of_decode fullCode DONE** (no hdrop).
              **Pure field5+hcre DONE**: encodeItems offset algebra;
              `extractSuccess_creation_type234_field5_pfx80` /
              `_hcre` / fit-gated `_hdec5`.               **srcOff chain + short hnext DONE**:
              `shortListSrcOff` / `encodeItemsPrefixLen_succ` /
              `hnext_short_string_of_decode`. **Empty-field packaging hnext DONE**:
              `hnext_empty_short_of_pfx80` /
              `hnext_empty_matches_srcOff_succ` (decode-gated next =
              txBase+shortListSrcOff(n+1)). Residual: wire packaging
              **decode-gated packaging hnext* DONE** (wn0..wn4 OkConcrete keep
              pure like wn5; MidChainDecode ToWn5 pure_pre + hnext decode→next;
              Front/Assumed of_decode cascade).
              **pure packaging hnext helpers DONE**:
              `encode_item_length_le_encodeItems` / `_le_55_of_short_list`,
              `txBase_add_srcOff_add_nat`,
              `hnext_single_matches_srcOff_succ`,
              `extractSuccess_creation_type234_hcre_srcOff` /
              `_hnext_field5` (srcOff:=shortListSrcOff under creation type234 short).
              **multi-byte short-string packaging hnext DONE**:
              `encode_bytes_short_string` / `_length`,
              `encode_bytes_long_length_gt`,
              `bytes_data_length_le_55_of_encode_le`,
              `hnext_short_string_matches_srcOff_succ`,
              `hnext_bytes_matches_srcOff_succ` (unified empty/single/multi ≤55).
              **any-item packaging hnext DONE**:
              `hnext_short_list_matches_srcOff_succ` +
              `hnext_item_matches_srcOff_succ` (bytes or nested short list under
              short outer list; covers all short-list fields).
              **Assumed pureHlsHll DONE** + **hss pure room** +
              **Assumed pureHss DONE** (`pureHss`/`_fullCode`): hss0..5 via
              `hss_of_short_list_item` (fields 0..4 Or.inl hnext_fields04;
              field5 needs `7 ≤ items.length`); residual `hvalid1_*` at
              srcOff+1. **pure hinb/hcur/hdec-empty at list-end DONE**
              (`hinb_short_list_end`, `packaging_hcur_shortListSrcOff0`,
              `hdec_empty_short_list_end`). **short endPtr/cursor bridge DONE**:
              `short_walk_init_end_eq_shortListEndPtr`,
              `short_walk_init_cursor_eq_srcOff0`, `packaging_short_endPtr`,
              `rlpItemDecode_single_byte` / `hdec_single_short_list_end`.
              **concrete short AfterSave→creation of_decode DONE**
               (`frontAfterSavePostShort_to_midJoinPre`;
               `extractFrontAfterSaveCreation_then_epi_of_decode_short` —
               concrete hcur/hdec/hinb/hnext/hcre at shortWalkEnd, no ∀endPtr;
               pure `shortWalkCursor_eq_srcOff0` / `shortWalkEnd_eq_shortListEndPtr`).
               **short concrete E→ret + Assumed DONE**
               (`extractFrontToAfterSave_short_concrete`;
               `extractFrontCreation_then_epi_of_decode_short_concrete`;
               `extractAssumed_creation_fullCode_of_decode_short_concrete` —
               no ∀endPtr on hcur/hdec/hinb; still residual walk statics
               hoff/hss/hdec concrete + hnext/hcre at shortWalkEnd).
                **short concrete pure wire DONE**
                (`extractAssumed_creation_shortConcrete_pure(_fullCode)`):
                discharges hcur/hnext/hcre/hinb/hoff/hover/hls/hll/hne + short
                walk guards from extractSuccess+shortListSrcOff.
                **pure hdec DONE** (`hdec_short_list_item` /
                `extractAssumed_creation_shortConcrete_pureHdec(_fullCode)`).
                **pureHvalid DONE** (`validByteRange` collapse;
                `extractAssumed_creation_shortConcrete_pureHvalid(_fullCode)`).
                **ExtractAssumed static domain DONE** (txBase align/hover/
                `validByteRange`; toBuf align/over/`isValidMemAccess`;
                TIS derives type `hvalid0` via `validByteRange_head`).
                **Assumed-shaped creation type234 short DONE**
                (`extractAssumed_success_flat_creation_type234_short` under
                `extractCreationType234ShortPath`; classical-3 fullCode).
                **copy short concrete E2E DONE**
                (`extractFrontAfterSaveCopy_then_epi_of_decode_short`,
                `extractFrontCopy_then_epi_of_decode_short_concrete`).
                **copy Assumed short concrete DONE**
                (`extractAssumed_copy_fullCode_of_decode_short_concrete`:
                Assumed**contentDwords under honesty hyps).
                **copy pure field5 0x94 DONE**
                (`encode_bytes_len20_pfx`, `extractSuccess_copy_type234_field5_pfx94`,
                `_hlen20`, `_hnext_content`, `_hnext_hlen20_srcOff` packaging).
                **copy Assumed pure wire DONE**
                (`extractAssumed_copy_shortConcrete_pure(_fullCode)`:
                shortListSrcOff + hnext/hlen20/hnext_content pure;
                Assumed**contentDwords). **type234 short creation bare Assumed path Prop DONE**; **type234 short copy Assumed**content path Prop DONE**. **legacy of_decode AfterSave→creation DONE** (`TopMidSeq/Chain/JoinLegacyDecode`). **legacy short creation bare Assumed path Prop DONE** (`extractAssumed_success_flat_creation_legacy_short` under `extractCreationLegacyShortPath`; classical-3). **t1 of_decode AfterSave→creation DONE** (`TopMidSeq/Chain/JoinT1Decode`; classical-3). **t1 short Front E2E+Assumed packaging DONE** (`TopFrontCreDecodeShortT1`/`E2EShortConcreteT1`/`AssumedShortConcreteT1`; classical-3). **t1 short creation bare Assumed path Prop DONE** (`extractAssumed_success_flat_creation_t1_short`).
                **copy content-from-bytesRegion leaf DONE**
                (`bytesRegion_dword_triple_at` + `extractCopyPath_region` classical-3;
                split/rejoin partition, no additive contentDwords). HaveField/MidJoin/Front short bare copy region DONE classical-3.
                **Assumed bare packaging DONE** (`TopAssumedCopyRegion`:
                `copyPost_to_assumed_region`,
                `extractAssumed_copy_of_front_short_concrete_region`,
                `_fullCode_of_decode_short_concrete_region`).
                **bare Assumed copy path Prop DONE**
                (`extractAssumed_success_flat_copy_type234_short`,
                gate `srcOff5+1=8*q`). **Bare Assumed short copy path Props DONE** (type234+legacy+t1 region).
                Long type234 creation bare Assumed DONE. Long type234 creation+copy bare Assumed path Props DONE (copy gates longListSrcOff5+1=8*q). Residual: legacy/t1 long; multi-tx Option A; Teer; gate.
                content offset 8-aligned); long-list; multi-tx ambient Option A;
                Teer prover1; gate a4gbr.1.
            **fullCode ∪ extract(+walks) DONE** (`fullCode = (tis∪ets)∪extractLinkedCode`;
            `extractLinked_mono` / `extract_mono_full` / `type_mono`).
            ~~TypeDispatchAssumed~~ DONE — use `typeDispatch_discharged`

  4. ~~BgvOffsetAssumed~~ DONE — use `bgvOffset_discharged`
  5. Full eip8037_tx_gas_gate composition (separate residual of a4gbr.1)

  This module holds the residual inventory and import hooks. Concrete
  compose theorems land when prover1 teer top is available.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayTop
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasDischarge
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasDischargeAmbient
import EvmAsm.Codegen.Programs.BgvOffsetDischarge
import EvmAsm.Codegen.Programs.TxTypeDispatchTisDischarge
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbientOff0
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedPureHvalidT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHvalidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHvalidLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHvalidT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressExtractAssumedDischarge
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLongRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLongLegacyRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyPureHvalidLongT1Region
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArrayCompose

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
  (BgvOffsetAssumed nIntrinsicSteps nIntrinsicStackDwords tisScratchOwn fullCode
    bgvOffsetAssumed_fullCode)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (TisCalleeAssumptions ExtractAssumed ExtractEntry TypeEntry LinkEts T
    TypeDispatchAssumed intrinsicAssumed_success_flat_off0
    intrinsicAssumed_success_flat_off0_own)
open EvmAsm.Codegen.TxTypeDispatchSpec (typeDispatchAssumed_fullCode)
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
  (TeerApplied pureIntrinsicStateGasSuccess)

/-- Discharged loop-site bgv contract. Pass as `hbgv` to
    `blockVerdictTxStateGasArray_bal0/balNez_spec_within`. -/
def bgvOffset_discharged : BgvOffsetAssumed fullCode :=
  bgvOffsetAssumed_fullCode

/-- Discharged type_dispatch contract for intrinsic TisCalleeAssumptions. -/
def typeDispatch_discharged : TypeDispatchAssumed TxIntrinsicStateGasSpec.fullCode :=
  typeDispatchAssumed_fullCode

/-- Assumed-shaped extract discharge for short type234 creation path.
    Full `ExtractAssumed.success_flat` still residual (other success arms). -/
def extract_discharge_creation_type234_short_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_type234_short

/-- Long type234 creation bare Assumed path Prop available under fullCode. -/
def extract_discharge_creation_type234_long_available :=
  @EvmAsm.Codegen.TxExtractToAddressSpec.extractAssumed_success_flat_creation_type234_long


def extract_discharge_creation_legacy_long_available :=
  @EvmAsm.Codegen.TxExtractToAddressSpec.extractAssumed_success_flat_creation_legacy_long

def extract_discharge_creation_t1_long_available :=
  @EvmAsm.Codegen.TxExtractToAddressSpec.extractAssumed_success_flat_creation_t1_long


def extract_discharge_creation_legacy_short_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_legacy_short

def extract_discharge_creation_t1_short_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_t1_short

/-- Copy path packaging under Assumed**contentDwords (legacy content packaging). -/
def extract_discharge_copy_type234_short_available :=
  TxExtractToAddressSpec.extractAssumed_content_copy_type234_short

/-- Bare Assumed copy path (region partition; dword-aligned content). -/
def extract_discharge_copy_type234_short_region_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_type234_short

def extract_discharge_copy_type234_long_region_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_type234_long

def extract_discharge_copy_legacy_long_region_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_legacy_long

def extract_discharge_copy_legacy_short_region_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_legacy_short

def extract_discharge_copy_t1_short_region_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_t1_short

def extract_discharge_copy_t1_long_region_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_t1_long

/-- Residual inventory for the unconditional a4gbr deliverable.
    BgvOffset + TypeDispatchAssumed removed — use `*_discharged`. -/
structure A4gbrResiduals where
  /-- ExtractAssumed path Props bare DONE short+long all types; residual is
      ambient re-spec (bytesRegion regionBase blob) for multi-tx off≠0. -/
  extract : ExtractAssumed TxIntrinsicStateGasSpec.fullCode
  /-- Multi-tx ambient Option A progress classical-3:
      * type_dispatch ambient full off/len: `typeDispatchAssumedAmbient_fullCode`
       * extract ambient body dual progress:
         off0 lemma + path package; pure bridges `txSlice_getElem`/`loadPtr_add_rel_eq`/`ambientAbsOff`;
         type_dispatch call ambient DONE (`extractTypeSuccessAmbient`);
         load type/inner ambient DONE (`extractLoadTypeInnerAmbient`);
         type+load compose ambient DONE (`extractTypeThenLoadAmbient` E+72→E+144);
         walk_init short ambient DONE (`extractWalkInitCall_short_ambient` + guards);
         walk_next0 call ambient alias DONE; short fromTypeLoad ambient DONE;
         Front short AfterSave ambient concrete DONE
           (`extractWalkInitCall_short_toAfterSave_concrete_ambient`);
         split-base AfterSave frame + midJoin bridge DONE
           (`afterSaveFrameTyAmbient`, `frontAfterSavePostShortAmbient_to_midJoinPre`);
         type234 AfterSave→WalkNext0 ambient DONE (`extractType234ToWalkNext0_ambient`);
         wn0 call outcome ambient DONE (`extractWalkNext0Call_type234_outcome_ambient`);
         wn0 BNE/OkNested ambient DONE; ToWn0Ok of_decode ambient DONE
           (`extractType234ToWn0Ok_owned_of_decode_ambient`);
         wn1..5 PrepCallOk ambient DONE (`extractWalkNext{k}PrepCallOk_owned_of_decode_ambient`);
          ToWn5 chain ambient DONE (`extractType234ToWn5Ok_owned_of_decode_ambient`);
          MidOwned creation ambient DONE
            (`extractType234HaveFieldCreation_then_epi_ambient`);
          MidJoin AfterSave→creation ambient DONE
            (`extractType234AfterSaveCreation_then_epi_of_decode_ambient`);
           MidJoin AfterSave→copy region ambient DONE
             (`extractType234AfterSaveCopy_then_epi_of_decode_region_ambient`);
           Front E2E short creation ambient DONE
             (`extractFrontCreation_then_epi_of_decode_short_concrete_ambient`);
           Assumed ambient packaging under honesty DONE
             (`extractAssumed_creation_fullCode_of_decode_short_concrete_ambient`);
           AmbientPureBridge DONE (cursor/end/hnext/hcre/hss/walk guards);
           AmbientShortConcretePure DONE classical-3;
            AmbientPureHvalid + path Prop DONE classical-3
              (`extractAssumed_success_flat_creation_type234_short_ambient`);
            Front E2E short copy region ambient DONE
              (`extractFrontCopy_then_epi_of_decode_short_concrete_region_ambient`);
            Assumed copy packaging ambient DONE
              (`extractAssumed_copy_fullCode_of_decode_short_concrete_region_ambient`);
            Ambient copy PureHvalid + path Prop DONE classical-3
              (`extractAssumed_success_flat_copy_type234_short_ambient`;
               gate absOff_field5+1=8*q)
          * TIS ambient callees + framed: extract/type/ets framed
          * `txIntrinsicStateGas_success_spec_within_ambient` compose DONE
          * `intrinsicAssumed_success_flat_ambient(_own)` general off/len DONE
          * `TisCalleeAssumptionsAmbient` = extract ambient hyp + type ambient full
          * legacy frames ambient DONE; leg0..3 PrepCallOk + ToWalk3 of_decode ambient DONE
              (`extractLegacyToWalk3Ok_owned_of_decode_ambient`)
          * legacy MidJoin AfterSave→creation ambient DONE
              (`extractLegacyAfterSaveCreation_then_epi_of_decode_ambient`)
          * legacy MidJoin AfterSave→copy region ambient DONE
              (`extractLegacyAfterSaveCopy_then_epi_of_decode_region_ambient`)
          * legacy Front E2E short creation ambient DONE
              (`extractFrontCreation_then_epi_of_decode_short_concrete_legacy_ambient`)
          * Assumed packaging legacy short creation ambient DONE
          * t1 ambient Mid frames/walks/MidJoin cre+copy DONE
          * t1 short Front E2E + Assumed packaging ambient DONE
            * t1 short creation ambient PureHvalid path Prop DONE
            * t1 short copy ambient PureHvalid path Prop DONE
            * long type234 creation CreDecode/E2E/Assumed ambient DONE classical-3
            * long type234 creation ambient PureHvalid path Prop DONE classical-3
              (`extractAssumed_success_flat_creation_type234_long_ambient`;
               hitem0..5 short-encode bounds outside path)
            * long legacy creation ambient PureHvalid path Prop DONE classical-3
              (`extractAssumed_success_flat_creation_legacy_long_ambient`;
               hitem0..3 short-encode bounds outside path)
            * long t1 creation ambient PureHvalid path Prop DONE classical-3
              (`extractAssumed_success_flat_creation_t1_long_ambient`;
               hitem0..4 short-encode bounds outside path)
              (`extractAssumed_creation_fullCode_of_decode_short_concrete_legacy_ambient`)
          * legacy PureHvalid ambient path Prop DONE
              (`extractAssumed_success_flat_creation_legacy_short_ambient`)
          * legacy Front E2E short copy ambient + Assumed packaging DONE
              (`extractAssumed_copy_fullCode_of_decode_short_concrete_legacy_region_ambient`)
          * long legacy creation CreDecode/E2E/of_decode ambient DONE classical-3
          * long legacy creation Pure/PureHvalid ambient path Prop DONE classical-3
          Residual: long type234 copy ambient of_decode (CopyDecode/E2E/Assumed) DONE classical-3; residual: PureHvalid long copy + legacy/t1 copy ambient / long copy ambient;
            fill ExtractAssumedAmbient.success_flat case-split;
            package IntrinsicAssumed structure; Teer; gate. -/

  ambientMultiTx : True := trivial
  /-- Teer leaf modulo its remaining input callees (prover1 scope). -/
  teerInputCallees : True := trivial

/-- Ambient general off/len IntrinsicAssumed-shaped discharge available
    (under TisCalleeAssumptionsAmbient + extractSuccess/type success/statics). -/
def intrinsic_discharge_ambient_available :=
  TxIntrinsicStateGasSpec.intrinsicAssumed_success_flat_ambient_own

/-- Slice-eq-ambient discharge is available (off=0, full blob).
    Packaging into `IntrinsicAssumed` for arbitrary off/len remains residual. -/
theorem intrinsic_discharge_off0_available
    (asm : TisCalleeAssumptions TxIntrinsicStateGasSpec.fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : EvmAsm.Codegen.TxExtractToAddressModel.extractSuccess bs)
    (hsuccess : (EvmAsm.Codegen.TxTypeDispatchSpec.teerTxTypeDispatch bs).1 =
      (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : EvmAsm.Rv64.SAsm.DualReadByteScan.validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess
      (EvmAsm.Codegen.TxIntrinsicStateGasSpec.ToBufAddr + (16 : Word)) = true) :
    let lenW := BitVec.ofNat 64 bs.length
    cpsTripleWithin nIntrinsicSteps T ret TxIntrinsicStateGasSpec.fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ regionBase) **
        (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion regionBase bs **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
        (.x16 ↦ᵣ old16) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) :=
  intrinsicAssumed_success_flat_off0 asm hextract htype
    ret spVal regionBase outPtr oldOut s0 s1 s2 s3 s4 s5 s6 s7 bs
    old5 old6 old7 old13 old14 old15 old16 hret hlink hextractOk hsuccess halign hover hvalidBuf htvalid

/-- Same as `intrinsic_discharge_off0_available` with regOwn temps
    (IntrinsicAssumed footprint). Multi-tx off≠0 still residual. -/
theorem intrinsic_discharge_off0_own_available
    (asm : TisCalleeAssumptions TxIntrinsicStateGasSpec.fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : EvmAsm.Codegen.TxExtractToAddressModel.extractSuccess bs)
    (hsuccess : (EvmAsm.Codegen.TxTypeDispatchSpec.teerTxTypeDispatch bs).1 =
      (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : EvmAsm.Rv64.SAsm.DualReadByteScan.validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess
      (EvmAsm.Codegen.TxIntrinsicStateGasSpec.ToBufAddr + (16 : Word)) = true) :
    let lenW := BitVec.ofNat 64 bs.length
    cpsTripleWithin nIntrinsicSteps T ret TxIntrinsicStateGasSpec.fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ regionBase) **
        (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion regionBase bs **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) :=
  intrinsicAssumed_success_flat_off0_own asm hextract htype
    ret spVal regionBase outPtr oldOut s0 s1 s2 s3 s4 s5 s6 s7 bs
    hret hlink hextractOk hsuccess halign hover hvalidBuf htvalid

/-- Multi-tx Option A: ambient TypeDispatchAssumed full off/len available. -/
def type_dispatch_ambient_discharged :=
  TxTypeDispatchSpec.typeDispatchAssumedAmbient_fullCode

/-- Multi-tx Option A: ambient ExtractAssumed short type234 creation path Prop. -/
def extract_discharge_creation_legacy_short_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_legacy_short_ambient

/-- Multi-tx Option A: ambient ExtractAssumed short t1 creation path Prop. -/
def extract_discharge_creation_t1_short_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_t1_short_ambient

/-- Multi-tx Option A: ambient ExtractAssumed short t1 copy path Prop. -/
def extract_discharge_copy_t1_short_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_t1_short_ambient

/-- Residual discharge hook: ambient ExtractAssumed short legacy copy path Prop. -/
def extract_discharge_copy_legacy_short_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_legacy_short_ambient

def extract_discharge_creation_type234_short_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_type234_short_ambient

/-- Multi-tx Option A: ambient ExtractAssumed long type234 creation path Prop. -/
def extract_discharge_creation_type234_long_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_type234_long_ambient

def extract_discharge_creation_legacy_long_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_legacy_long_ambient

def extract_discharge_creation_t1_long_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_creation_t1_long_ambient

/-- Multi-tx Option A: ambient ExtractAssumed short type234 copy path Prop. -/
def extract_discharge_copy_type234_short_ambient_available :=
  TxExtractToAddressSpec.extractAssumed_success_flat_copy_type234_short_ambient

#print axioms intrinsic_discharge_off0_available
#print axioms intrinsic_discharge_off0_own_available
#print axioms bgvOffsetAssumed_fullCode
#print axioms typeDispatchAssumed_fullCode
#print axioms type_dispatch_ambient_discharged
#print axioms TxExtractToAddressSpec.extractAssumed_ambient_off0
#print axioms TxExtractToAddressSpec.extractAssumed_ambient_creation_type234_short_off0
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_creation_legacy_short_ambient
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_creation_t1_short_ambient
#print axioms extract_discharge_creation_t1_short_ambient_available
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_copy_t1_short_ambient
#print axioms extract_discharge_copy_t1_short_ambient_available
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_copy_legacy_short_ambient
#print axioms extract_discharge_copy_legacy_short_ambient_available
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_creation_type234_short_ambient
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_creation_type234_long_ambient
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_creation_legacy_long_ambient
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_creation_t1_long_ambient
#print axioms extract_discharge_creation_t1_long_ambient_available
#print axioms TxExtractToAddressSpec.extractAssumed_success_flat_copy_type234_short_ambient

end EvmAsm.Codegen.BlockVerdictTxStateGasArrayCompose
