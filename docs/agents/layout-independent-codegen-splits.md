# Layout-independent Codegen splits

Guest layout changes regenerate `GuestAddrs` and linked address facts.  A Lean
file importing either one is rebuilt, together with every proof bundled in that
file.  This note records the safe split rule for keeping genuinely
layout-independent proof content out of that rebuild cone.

## Rule for a safe split

Move a declaration into a sibling module only when all of the following hold:

1. Its type and proof body mention neither `GuestAddrs`, `RegionMap`, a linked
   program entry/base, `laHi`/`laLo`/`jalOff`, nor an emitted-program
   `CodeReq` tied to a linked address.
2. Every import needed by the sibling is itself outside the layout cone.  A
   declaration can look address-free while depending on a helper from a file
   that imports `GuestAddrs`; that is **not** a useful split.
3. The sibling imports only the smallest core/RV64/EL modules it needs; do not
   import the original layout-dependent parent merely for convenience.
4. Preserve the declaration statement and proof verbatim.  The parent imports
   the sibling and rewrites only its local qualified name/open declaration.
5. Build the sibling and parent together, run `check-unimported.sh`, and run
   the affected byte/layout gates.  This is a build-graph refactor, not a
   semantics or emitted-byte change.

## Completed exemplar: logs-bloom copy arithmetic

`LogsBloomCopyArithmetic.lean` contains the four Word/Nat facts shared by:

- `HeaderExtractLogsBloomSpec.lean` (1,421 lines): `helb_succ_dec`,
  `helb_succ_ne_zero`, `helb_advance`, and `helb_ofNat_toNat`;
- `ReceiptExtractLogsBloomSpec.lean` (1,362 lines): their `relb_*`
  counterparts.

The sibling imports only `EvmAsm.Rv64.Instructions`; it has no Codegen layout
or emitted-program import.  Both former layout-dependent proof files now only
import the sibling for those facts.  This is also a useful template for paired
header/receipt helpers: make the shared arithmetic generic rather than moving
two renamed copies.

## Candidate queue for mechanical follow-up

| Source file | Proposed sibling | Layout-free content | Caution |
| --- | --- | --- | --- |
| `Programs/RlpListNthItemSAsmBase.lean` (1,356 lines) | `RlpListNthItemStrictList.lean` | `StrictListPayload` plus its structural lemmas through `long_view` (before the first `BalAccountNonstorageFinalsSpec` use) | Stop before `noStrictList_of_long_nonminimal`: it uses a helper from the layout-dependent BAL proof chain. |
| `Programs/RlpSpliceHelperSpec.lean` (1,380 lines) | `RlpSpliceHelperArithmetic.lean` | `toNat_zx`, `ult_zx_of_lt`, `not_ult_zx_of_ge`, `ris_result_128`, `ris_result_192` | The following `∀ base` triples still import `RlpRead`, which is layout-dependent; do not move them without first splitting `RlpRead`. |
| `Programs/HeaderExtractLogsBloomSpec.lean` | `LogsBloomCopyArithmetic.lean` | Completed exemplar | Keep `helbMem`, `helbBase`, LA/JAL proofs, and all `CodeReq` facts in the parent. |
| `Programs/ReceiptExtractLogsBloomSpec.lean` | `LogsBloomCopyArithmetic.lean` | Completed exemplar | Same boundary as header. |

## Explicit non-candidates until dependencies are split

- `RlpFieldToU64SAsm.Result` is syntactically semantic, but it refers to
  `RlpListNthItemSAsm.Failure` and `Success`; splitting it alone retains the
  layout-dependent import edge.
- `RlpSpliceHelperSpec`'s linked `rlp_item_size` and
  `rlp_encode_list_prefix` wrappers, and `AccountAccessorTopSpec`, are pinned
  to concrete `GuestAddrs` bases or JAL/LA facts.
- The remaining `RlpListNthItemSAsmBase` strict-walk construction and prefix
  lemmas import `BalAccountNonstorageFinalsSpec` helpers.  They need a core
  replacement for those helpers before a split buys rebuild isolation.

The mechanical bulk should apply this rule one sibling at a time, preserve
file-local namespaces, and use a build gate after each batch rather than a
global textual extraction.
