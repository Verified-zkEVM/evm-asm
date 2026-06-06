# EEST account-INSERT — handoff (for the next agent)

You are the evm-asm BEADS worker (WORKER_ID=c1). Standing goal: **finish full
EEST passing** — make the Lean-verified RV64 `run_stateless_guest` (run on
ziskemu) produce real, sound full-matches on the EEST `zkevm@v0.4.0` (Amsterdam)
fixtures, reported by `scripts/codegen-eest-stateless-check.sh`, WITHOUT
soundness regressions (must never false-positive an invalid block). Follow
`LOOP.md`. Hard rules: never `gh pr merge`/`review --approve`/`issue close`;
never bump `maxHeartbeats`/`maxRecDepth`; no `native_decide`/`bv_decide`; all
RV64 mem access naturally aligned (no-misaligned invariant); PR body trailer
"Authored by @pirapira; implemented by Claude Code"; commit trailer
"Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>".

## The one thing blocking progress right now

**`bd show evm-asm-fhsxz.2.4.2.6.6`** — claim it. The account-INSERT engine is
built+verified and wired into the verdict, but the wiring computes a WRONG
post-state root on real eip4895 precompile/nonexistent-account blocks, so the
expected eip4895 jump (24/140 → ~114/140 sound full-matches) has NOT landed.
The wiring is SOUND (0 false positives, no regression — a wrong root just yields
a conservative verdict 0), it just doesn't help yet.

### What is proven (do NOT re-litigate)
- The verdict is sound & green-lit: PR #7758, 0 FP across a 1200-fixture scan.
- eip4895 baseline = **24/140** sound full-matches, 0 FP (after the zero-amount
  skip, PR #7761).
- The whole DB-aware MPT-insert engine is **verified correct in isolation** via
  ~12 ziskemu vectors (all PASS): branch-empty depth 0/1/2, leaf-split m=0/m>0
  depth 0/1, empty-trie, ext-then-branch, DB-resident-root descent,
  DB-modified-intermediate descent, 64-nibble account-key insert
  (`mi_acctkey`), DB-root + 64-nibble insert (`state_root_ins_longkey`).
- For `bal_withdrawal_to_precompiles[0x01]`: the ASM's **system-only** root
  (first 2 changes = EIP-2935 + EIP-4788) = `4c2f44dd…` = Python
  `patricialize(post − new account)` EXACTLY. So the system writes are correct.
  The full root = `193e1f61…` ≠ expected `e5767b92…`. **So the bug is purely
  inserting the precompile account into the (correct) R2.** Divergence case =
  BRANCH_EMPTY_SLOT at depth 0 (root branch, nibble 1).
- The single-block source-fixture diff CONFIRMS there is NO unmodeled state:
  the per-block change is exactly {2935 1 slot, 4788 1 slot, new 0x01 account
  with balance = amount·1e9 = 10 Gwei}. It is an asm bug, not missing semantics.

### Lead hypothesis — REFUTED by static audit (2026-06-06); do NOT chase
The original hypothesis was: the INSERT fills an **empty** slot, growing the
branch ~33 bytes across the RLP multi-byte length-prefix boundary (`0xc0+len`
→ `0xf8 LL` at 56, or `0xf8 LL` → `0xf9 LLLL` at 256), and `mpt_splice_slot`
(Programs/MptSet.lean) emits a stale prefix because no synthetic vector ever
grew a branch *across* that boundary.

A line-by-line static audit refuted this: `mpt_splice_slot` recomputes
`new_payload_len = head_len + new_ref_len + tail_len` from scratch and calls
`rlp_encode_list_prefix` fresh on every splice (MptSet.lean:430-438); the
head/tail copies start at `payload_start`, never including the old prefix; and
`rlp_encode_list_prefix` (RlpRead.lean:380-433) is correct on both the 55/56
and 255/256 boundaries (byte-count ladder + BE emit loop checked by hand).
Child refs are re-derived via `mpt_node_slot_encode` after each splice, so the
inline/hash threshold is also absorbed. The prefix-boundary synthetic vector
(old step 1 below) would pass and prove nothing.

Remaining suspects, in rough priority order:
* the **node-DB threading** between change 2 (MODIFY via `mpt_set_acc`) and
  change 3 (INSERT via `mpt_insert_acc`) — i.e. `mpt_node_resolve` finding the
  DB-modified root branch produced by the first two changes;
* `mpt_insert_walk_db` depth/`consumed` bookkeeping for the depth-0
  BRANCH_EMPTY_SLOT case;
* `rlp_item_span` walking a 17-item root branch whose children mix inline
  (<32 B) and hash refs.

### How to confirm / fix
1. Go straight to the **witness-model**: extend
   `scripts/eest_diag_patricialize.py` to parse the zkevm input's SSZ witness
   section into a `{keccak:node}` DB, set the pre-root, and replay the 3 changes
   node-by-node; OR instrument `mpt_insert_acc` to dump the spliced root-branch
   bytes + the new leaf bytes to spare OUTPUT bytes and diff them against the
   Python model to find the first divergent node.
2. (Superseded — refuted above.) The prefix-boundary `MI_VECTORS` vector via
   `scripts/codegen-zisk-mpt-insert-check.sh` is no longer the lead; only add
   it as a regression vector after the real bug is found.

### Reproduce in ~30s
```
# (already-generated) eip4895 probe inputs + manifest:
ls gen-out/v2-eip4895/manifest.tsv
# build the wired verdict probe (on branch feat/eest-insert-integration):
git checkout feat/eest-insert-integration
lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o gen-out/zisk_stateless_verdict_v2
# run one precompile fixture; block_verdict DEBUG writes:
#   OUTPUT+0 verdict bit | OUTPUT+1 block_state_root status |
#   OUTPUT+64 R_asm (recomputed) | OUTPUT+96 expected payload.state_root |
#   OUTPUT+128 system-only root (first 2 changes)
lab=$(awk -F'\t' 'index($1,"to_precompiles_fork_Amsterdam-0x01"){print $1;exit}' gen-out/v2-eip4895/manifest.tsv)
inp=$(awk -F'\t' -v L="$lab" '$1==L{print $2}' gen-out/v2-eip4895/manifest.tsv)
~/.zisk/bin/ziskemu -e gen-out/zisk_stateless_verdict_v2.elf -i "$inp" -o /tmp/d.out -n 200000000
od -An -tx1 -j64 -N32 /tmp/d.out   # R_asm = 193e1f61… (wrong)
od -An -tx1 -j96 -N32 /tmp/d.out   # expected = e5767b92…
od -An -tx1 -j128 -N32 /tmp/d.out  # system-only = 4c2f44dd… (CORRECT, == Python)
# Python reference roots:
uv run --directory execution-specs --quiet python3 "$PWD/scripts/eest_diag_patricialize.py" \
  "$PWD/$(find gen-out/eest-fixtures -name bal_withdrawal_to_precompiles.json|head -1)" "0x01-blockchain"
```

### When fixed
- Re-run the eip4895 probe loop over all 140 fixtures (status byte = `od -j0 -N1`
  of each output) — expect sound_full to jump well above 24, FALSE_POS=0.
- Re-run the FP gate on the 106 invalid-block (succ=0) fixtures in
  `gen-out/v2fp-run/manifest.tsv` — must stay FALSE_POS=0.
- **Remove the DEBUG instrumentation** from `block_state_root` /`block_verdict`
  in `EvmAsm/Codegen/Programs/BlockVerdict.lean` (the OUTPUT+1/+64/+96/+128 dumps,
  the `n=2` debug `mpt_state_root_ins` call, and `bsr_dbgroot`) before opening a
  PR. Then the wiring becomes PR-ready (stack it on `feat/eest-fullmatch`).

## Branch / PR map (all OPEN, stacked — the insert engine, verified)
```
main
 └─ #7758 feat/eest-fullmatch        block_verdict (green-lit, 0 FP)
     ├─ #7761 feat/eest-withdrawal-zero-skip   zero-amount skip (+20 → 24/140)
     └─ #7762 feat/mpt-insert-walk             mpt_insert_walk (divergence classify)
         └─ #7763 feat/mpt-insert              mpt_insert (branch-empty + empty-trie)
             └─ #7764 feat/mpt-insert-leaf-split   LEAF_SPLIT restructure
                 └─ #7765 feat/mpt-insert-acc      mpt_insert_walk_db (DB-aware walk)
                     └─ #7766 feat/mpt-insert-acc2     mpt_insert_acc (DB-aware insert)
                         └─ #7767 feat/mpt-state-root-ins  mpt_state_root_ins (driver)
                             └─ #7768 feat/mpt-insert-acc-deepfix  deep+dbchild+leafsplit-d1 vectors
```
**WIP wiring**: branch `feat/eest-insert-integration` (HEAD `c04466740`) =
merge of `feat/eest-withdrawal-zero-skip` + `feat/mpt-insert-acc2` + the `.3`
wiring (block_state_root builds a fresh account on mpt_walk not-found, records
40-byte INSERT/MODIFY change descriptors with `is_insert@32`, calls
`mpt_state_root_ins`) + the DEBUG instrumentation. Builds; sound; wrong-root bug
above. EXT-split inserts are conservative (status 1 → miss); that's bead
`evm-asm-fhsxz.2.4.2.6.4`'s remaining half (rare; not the blocker).

## Files
- `EvmAsm/Codegen/Programs/BlockVerdict.lean` — block_state_root / block_verdict
  / stateless_verdict_v2 + both function closures + the data section (has the
  insert scratch + `bsr_empty_account` + the DEBUG dumps).
- `EvmAsm/Codegen/Programs/MptInsert{Walk,WalkDb,Acc}.lean`, `MptStateRootIns.lean`
  — the insert engine.
- `EvmAsm/Codegen/Programs/MptSet.lean` (`mpt_splice_slot`, the prime suspect),
  `MptSetAcc.lean` (node DB, `mpt_set_acc`, `mpt_set_record_walk_db`).
- `scripts/mpt_ref.py` — vectors + `account_encode` + the trie primitives.
- `scripts/eest_diag_patricialize.py` — full-alloc reference (reproduces fixture
  pre/post roots, classifies an insert's divergence case).
- `scripts/codegen-zisk-mpt-{insert,insert-walk,state-root-ins}-check.sh` — checks.

## Beads
- `evm-asm-fhsxz.2.4.2.6.6` — THE debug bead (P0). Start here.
- `evm-asm-fhsxz.2.4.2.6` — parent (account INSERT for absent recipients).
- `evm-asm-fhsxz.2.4.2.6.3` — the integration (wiring) bead.
- `evm-asm-fhsxz.2.4.2.6.4` — LEAF_SPLIT done; EXTENSION_SPLIT still conservative.
- `evm-asm-fhsxz` — the EEST full-match epic.
