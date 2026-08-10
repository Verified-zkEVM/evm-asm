#!/usr/bin/env python3
"""code-1 leaf decoder: name which account/field diverges on bv_fail=1 rows.

A state-root mismatch (#11547) is a 32-byte digest over the whole trie — it
does not say WHICH account or field diverged. This instrument:

  1. Runs the guest under spike with SPIKE_DUMP of sv_recomputed + account_writes
  2. Loads the fixture case (matched by statelessInput/Output bytes, not by name)
  3. Compares patricialize(postState) to sv_recomputed (NOT out[0:32] — see #11547)
  4. Emits per-row field records from account_writes vs postState
  5. Optionally ablates postState (single- and multi-account) until the guest root
     is reproduced, naming a minimal account/field set

Cluster by (field_class, account) — never by fixture-family label (beacon_root /
multi_block / buffer_wraparound were co-occurrences, not mechanisms).

Usage:
  scripts/code1-leaf-decoder.py \\
      --elf path/to/stateless_guest.elf \\
      --ids 00026,01308,01114 \\
      --out /tmp/leaf.tsv

  scripts/code1-leaf-decoder.py --elf ELF --fr-list /tmp/opencode/hist/fr_bv1.ids \\
      --limit 30 --out /tmp/leaf30.tsv

Environment:
  EEST_FIXTURES_DIR  fixture root containing blockchain_tests/...
                     (default: gen-out/eest-fixtures/tests-zkevm@v0.6.2/fixtures/fixtures)
  MANIFEST           default /var/tmp/fc668/manifest.tsv
"""
from __future__ import annotations

import argparse
import copy
import csv
import json
import os
import struct
import subprocess
import sys
import tempfile
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import eest_diag_patricialize as P  # noqa: E402

SPIKE = str(Path(__file__).resolve().parent / "spike" / "spike_run")
DEFAULT_MANIFEST = "/var/tmp/fc668/manifest.tsv"
DEFAULT_FXROOT = (
    Path(__file__).resolve().parents[1]
    / "gen-out/eest-fixtures/tests-zkevm@v0.6.2/fixtures/fixtures"
)

# Fallback absolute addresses when nm is unavailable (main 14e3fb2e7 era).
# Prefer nm resolution from --elf.
# account_writes_area is RegionMap-only (no nm symbol). Keep in lockstep with
# EvmAsm/Codegen/RegionMap.lean account_writes_area (0xbdb80000). Stale
# 0xA28A0000 predated the AW relocation and silently dumped the wrong arena.
FALLBACK_SYMS = {
    "sv_recomputed": 0xA46940E0,
    "account_writes_count": 0xB9A7F318,  # nm moves with .bss; prefer --elf nm
    "account_writes_area": 0xBDD80000,  # RegionMap.lean — not an nm symbol
}

AW_STRIDE = 128
AW_MAX_ROWS = 128

# account_writes `+112` validMask bits (GH #11736).  A FLAG says whether a field
# is MEANINGFUL; the field says what it is.  Reading an unset field as data is the
# defect this decoder had: a clear balance bit means the balance is UNSPECIFIED,
# not zero, so comparing it against a nonzero expectation invents a mismatch.
VM_BALANCE = 0x1
VM_NONCE = 0x2
VM_CODE = 0x4
VM_STATE = 0x8
VM_TOUCHED = 0x20

# Classes that are NOT defects: informational records a reader must not treat as
# findings.  Kept out of the primary work-list and out of the diverging-leaf count.
NON_DEFECT_CLASSES = (
    "guest_absent_ok",
    "balance_unspecified",
    "nonce_unspecified",
    "enumeration_entry_touched_only",
    "storage_in_separate_structure",
)


def nm_syms(elf: str) -> dict[str, int]:
    out = subprocess.check_output(["nm", elf], text=True, stderr=subprocess.DEVNULL)
    want = set(FALLBACK_SYMS)
    got: dict[str, int] = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) < 3:
            continue
        addr_s, _typ, name = parts[0], parts[1], parts[2]
        if name in want:
            got[name] = int(addr_s, 16)
    for k, v in FALLBACK_SYMS.items():
        got.setdefault(k, v)
    return got


def read_spkdmp(path: str) -> dict[int, bytes]:
    data = open(path, "rb").read()
    if data[:8] != b"SPKDMP01":
        raise ValueError(f"bad dump magic {data[:8]!r} in {path}")
    _ver, n = struct.unpack_from("<II", data, 8)
    off = 16
    ranges: dict[int, bytes] = {}
    for _ in range(n):
        addr, length = struct.unpack_from("<QQ", data, off)
        off += 16
        ranges[addr] = data[off : off + length]
        off += length
    return ranges


def load_manifest(path: str) -> list[list[str]]:
    rows = []
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            rows.append(line.split("\t"))
    return rows


def find_manifest_row(rows: list[list[str]], prefix: str) -> list[str] | None:
    for r in rows:
        if r[0].startswith(prefix) or r[0] == prefix:
            return r
    # bare 5-digit id
    for r in rows:
        if r[0].startswith(prefix + "_") or r[0][:5] == prefix:
            return r
    return None


def find_fixture_case(
    fxroot: Path, rel: str, body: bytes, exp_hex: str
) -> tuple[str, dict, int] | tuple[None, None, None]:
    """Return (case_key, fixture, block_index) matched by sob/sib, not by name."""
    path = fxroot / rel
    if not path.is_file():
        return None, None, None
    doc = json.load(open(path))
    er = bytes.fromhex(exp_hex[:64])
    for key, fx in doc.items():
        if not isinstance(fx, dict) or "blocks" not in fx:
            continue
        for bi, blk in enumerate(fx["blocks"]):
            sib_h = blk.get("statelessInputBytes") or ""
            sob_h = blk.get("statelessOutputBytes") or ""
            if not sib_h or not sob_h:
                continue
            sib = bytes.fromhex(sib_h[2:] if sib_h.startswith("0x") else sib_h)
            sob = bytes.fromhex(sob_h[2:] if sob_h.startswith("0x") else sob_h)
            if sob[:32] == er or sib in body or body == sib or body in sib:
                return key, fx, bi
    return None, None, None


def norm_addr(a: str) -> str:
    a = a.lower()
    if a.startswith("0x"):
        a = a[2:]
    return a.zfill(40)


def norm_alloc(alloc: dict) -> dict:
    return {norm_addr(k): v for k, v in alloc.items()}


def state_root(alloc: dict) -> bytes:
    return P.patricialize(norm_alloc(alloc))


def parse_aw_rows(area: bytes, count: int) -> list[dict[str, Any]]:
    rows = []
    n = min(count, len(area) // AW_STRIDE, AW_MAX_ROWS)
    for i in range(n):
        row = area[i * AW_STRIDE : (i + 1) * AW_STRIDE]
        addr = row[0:20].hex()
        bal = int.from_bytes(row[32:64], "big")
        nonce = struct.unpack_from("<Q", row, 64)[0]
        opt = struct.unpack_from("<Q", row, 72)[0]
        code_len = struct.unpack_from("<Q", row, 88)[0]
        flags = struct.unpack_from("<Q", row, 96)[0]
        vmask = struct.unpack_from("<Q", row, 112)[0]
        rows.append(
            {
                "addr": addr,
                "bal": bal,
                "nonce": nonce,
                "opt": opt,
                "code_len": code_len,
                "flags": flags,
                "vmask": vmask,
            }
        )
    return rows


def field_records(
    aw_rows: list[dict], pre: dict, post: dict
) -> list[dict[str, Any]]:
    """Compare account_writes rows to postState; emit field-level records."""
    pre_n, post_n = norm_alloc(pre), norm_alloc(post)
    recs: list[dict[str, Any]] = []
    seen = set()
    for r in aw_rows:
        addr = r["addr"]
        seen.add(addr)
        pe = post_n.get(addr)
        pr = pre_n.get(addr)
        base = {
            "account": addr,
            "vmask": f"0x{r['vmask']:x}",
            "opt": r["opt"],
            "guest_bal": r["bal"],
            "guest_nonce": r["nonce"],
            "guest_code_len": r["code_len"],
        }
        if r["opt"] == 0 and (r["vmask"] & 0x8):
            if pe is None:
                recs.append({**base, "field": "presence", "class": "guest_absent_ok",
                             "post": "absent", "guest": "Present-None"})
            else:
                recs.append({**base, "field": "presence", "class": "guest_absent_post_present",
                             "post": f"bal={pe.get('balance')}", "guest": "Present-None"})
            continue
        if pe is None:
            # GH #11736: a TOUCHED-only row carries no value bits. It is an
            # execution-map / root-enumeration entry, NOT a post-state delta, so
            # its absence from postState is expected and must not read as a
            # "guest-extra presence" finding.
            if not (r["vmask"] & (VM_BALANCE | VM_NONCE | VM_CODE | VM_STATE)):
                recs.append({**base, "field": "presence",
                             "class": "enumeration_entry_touched_only",
                             "post": "absent (expected)",
                             "guest": "touched-only row, no value bits set"})
                continue
            recs.append({**base, "field": "presence", "class": "guest_extra_not_in_post",
                         "post": "absent", "guest": f"bal={r['bal']} nonce={r['nonce']}"})
            continue
        exp_bal = int(pe.get("balance", "0x0"), 16)
        exp_nonce = int(pe.get("nonce", "0x0"), 16)
        code_hex = pe.get("code", "0x")
        exp_clen = (len(code_hex) - 2) // 2 if code_hex.startswith("0x") else len(code_hex) // 2
        # GH #11736: gate on the validMask bit ALONE.  The former condition was
        # `mask & bit OR guest_value OR expected_value`, whose trailing clauses
        # defeated the gate exactly when it mattered: an unset balance bit with a
        # nonzero expectation was reported as a mismatch (row 6295ee1b…, vmask
        # 0x3a). An unset field is UNSPECIFIED and is reported as such.
        if not (r["vmask"] & VM_BALANCE):
            recs.append({**base, "field": "balance", "class": "balance_unspecified",
                         "post": str(exp_bal),
                         "guest": "UNSPECIFIED (validMask balance bit clear)"})
        elif r["bal"] != exp_bal:
            recs.append({**base, "field": "balance", "class": "balance_mismatch",
                         "post": str(exp_bal), "guest": str(r["bal"])})
        if not (r["vmask"] & VM_NONCE):
            recs.append({**base, "field": "nonce", "class": "nonce_unspecified",
                         "post": str(exp_nonce),
                         "guest": "UNSPECIFIED (validMask nonce bit clear)"})
        elif r["nonce"] != exp_nonce:
            recs.append({**base, "field": "nonce", "class": "nonce_mismatch",
                         "post": str(exp_nonce), "guest": str(r["nonce"])})
        # code_len alone is weak (code body lives outside the row); only flag
        # when STATE valid and lengths clearly disagree on a non-empty side.
        if (r["vmask"] & 0x8) and r["code_len"] != exp_clen and (r["code_len"] > 0 or exp_clen > 0):
            recs.append({**base, "field": "code_len", "class": "code_len_mismatch",
                         "post": str(exp_clen), "guest": str(r["code_len"])})
        # storage root not in AW row — flagged separately if ablation says storage
        _ = pr  # kept for future pre-delta annotation
    # post accounts that changed from pre but never appear in AW
    for addr, pe in post_n.items():
        if addr in seen:
            continue
        pr = pre_n.get(addr)
        if pr == pe:
            continue
        # skip pure system-contract noise only if identical pre==post already handled
        diffs = []
        if (pr or {}).get("balance") != pe.get("balance"):
            diffs.append("balance")
        if (pr or {}).get("nonce") != pe.get("nonce"):
            diffs.append("nonce")
        if (pr or {}).get("code") != pe.get("code"):
            diffs.append("code")
        if (pr or {}).get("storage") != pe.get("storage"):
            diffs.append("storage")
        if diffs:
            # GH #11736: a storage-only delta has no counterpart here BY DESIGN --
            # `storage_writes` is a separate structure and
            # `execution_map_state_changes` enumerates the union -- so reporting it
            # as "absent from the account-writes arena" is a false residual. Say
            # where the counterpart lives instead of reporting an absence.
            if diffs == ["storage"]:
                recs.append({
                    "account": addr, "field": "storage",
                    "class": "storage_in_separate_structure",
                    "post": f"storage delta only ({len(pe.get('storage') or {})} slot(s))",
                    "guest": "not in account_writes by design; see storage_writes",
                    "vmask": "", "opt": "", "guest_bal": "", "guest_nonce": "",
                    "guest_code_len": "",
                })
                continue
            recs.append({
                "account": addr, "field": "+".join(diffs),
                "class": "post_delta_missing_from_aw",
                "post": f"bal={pe.get('balance')} nonce={pe.get('nonce')}",
                "guest": "no_aw_row",
                "vmask": "", "opt": "", "guest_bal": "", "guest_nonce": "",
                "guest_code_len": "",
            })
    return recs


def ablate(pre: dict, post: dict, guest_root: bytes, max_k: int = 3) -> list[tuple]:
    """Minimal account-level reverts of post→pre that reproduce guest_root."""
    pre_n, post_n = norm_alloc(pre), norm_alloc(post)
    if state_root(post_n) == guest_root:
        return [("", "MATCH_POST", "", "")]
    if state_root(pre_n) == guest_root:
        return [("", "MATCH_PRE", "", "")]

    diff_addrs = sorted(
        {a for a in set(pre_n) | set(post_n) if pre_n.get(a) != post_n.get(a)}
    )
    hits: list[tuple] = []

    def apply_reverts(addrs: tuple[str, ...]) -> dict:
        c = copy.deepcopy(post_n)
        for a in addrs:
            if a in pre_n:
                c[a] = copy.deepcopy(pre_n[a])
            else:
                c.pop(a, None)
        return c

    # single-field inside each differing account
    for addr in diff_addrs:
        pe = post_n.get(addr, {})
        pr = pre_n.get(addr)
        if pr is None:
            c = {k: v for k, v in post_n.items() if k != addr}
            if state_root(c) == guest_root:
                hits.append((addr, "ACCOUNT_REMOVE", "present", "absent"))
            continue
        for field in ("balance", "nonce", "code"):
            defv = "0x0" if field != "code" else "0x"
            if pe.get(field, defv) == pr.get(field, defv):
                continue
            c = copy.deepcopy(post_n)
            c[addr][field] = pr.get(field, defv)
            if state_root(c) == guest_root:
                hits.append((addr, field, pe.get(field, defv), pr.get(field, defv)))
        ps, qs = pr.get("storage") or {}, pe.get("storage") or {}
        if ps != qs:
            c = copy.deepcopy(post_n)
            c[addr]["storage"] = copy.deepcopy(ps)
            if state_root(c) == guest_root:
                hits.append((addr, "storage_ALL", None, None))
            for slot, val in qs.items():
                if ps.get(slot) == val:
                    continue
                c = copy.deepcopy(post_n)
                if slot in ps:
                    c[addr]["storage"][slot] = ps[slot]
                else:
                    del c[addr]["storage"][slot]
                if state_root(c) == guest_root:
                    hits.append((addr, f"storage:{slot}", val, ps.get(slot)))

    if hits:
        return hits

    # multi-account reverts (post → pre on whole account)
    for k in range(1, min(max_k, len(diff_addrs)) + 1):
        for combo in combinations(diff_addrs, k):
            c = apply_reverts(combo)
            if state_root(c) == guest_root:
                hits.append((",".join(combo), f"ACCOUNTS_REVERT_k{k}", "post", "pre"))
        if hits:
            break
    return hits


def run_guest(
    elf: str, inp: str, syms: dict[str, int], dump_path: str, out_path: str
) -> tuple[int | None, int | None, bytes | None, list[dict], int]:
    sv = syms["sv_recomputed"]
    awc = syms["account_writes_count"]
    awa = syms["account_writes_area"]
    ranges = f"0x{sv:x}:32,0x{awc:x}:8,0x{awa:x}:{AW_MAX_ROWS * AW_STRIDE}"
    env = {**os.environ, "SPIKE_DUMP_FILE": dump_path, "SPIKE_DUMP_RANGES": ranges}
    try:
        r = subprocess.run(
            [SPIKE, elf, inp, out_path],
            capture_output=True,
            timeout=180,
            env=env,
        )
        rc = r.returncode
    except subprocess.TimeoutExpired:
        return None, None, None, [], -9

    succ = bv = None
    if os.path.exists(out_path) and os.path.getsize(out_path) >= 120:
        b = open(out_path, "rb").read()
        succ = b[32]
        bv = struct.unpack_from("<Q", b, 112)[0]

    guest = None
    rows: list[dict] = []
    if os.path.exists(dump_path) and os.path.getsize(dump_path) > 16:
        R = read_spkdmp(dump_path)
        guest = R.get(sv)
        cnt = struct.unpack_from("<Q", R[awc], 0)[0] if awc in R else 0
        rows = parse_aw_rows(R.get(awa, b""), cnt)
    return succ, bv, guest, rows, rc


def decode_one(
    prefix: str,
    manifest_rows: list[list[str]],
    elf: str,
    fxroot: Path,
    syms: dict[str, int],
    work: Path,
    do_ablate: bool,
) -> dict[str, Any]:
    row = find_manifest_row(manifest_rows, prefix)
    if not row:
        return {"id": prefix, "err": "no_manifest"}
    label, inp, exp, exp_succ, rel = row[0], row[1], row[2], int(row[3]), row[6]
    if not os.path.isfile(inp):
        return {"id": prefix, "label": label, "err": "no_input"}
    body = open(inp, "rb").read()
    case_key, fx, bi = find_fixture_case(fxroot, rel, body, exp)
    if not fx:
        return {"id": prefix, "label": label, "err": "no_fixture_case", "rel": rel}

    pre, post = fx.get("pre") or {}, fx.get("postState") or {}
    nblocks = len(fx.get("blocks") or [])
    # Intermediate multi-block rows: final postState is not the block's post.
    post_usable = nblocks == 1 or bi == nblocks - 1
    post_root = state_root(post).hex() if post and post_usable else ""
    hdr = ""
    try:
        hdr = fx["blocks"][bi]["blockHeader"]["stateRoot"]
    except Exception:
        pass

    dump = str(work / f"{prefix}.bin")
    outp = str(work / f"{prefix}.out")
    succ, bv, guest, aw_rows, rc = run_guest(elf, inp, syms, dump, outp)
    if guest is None:
        return {
            "id": prefix, "label": label, "err": "no_sv_recomputed",
            "succ": succ, "bv": bv, "rc": rc, "case": case_key, "block": bi,
        }

    match = post_usable and guest.hex() == post_root
    recs = field_records(aw_rows, pre, post) if post_usable else []
    # GH #11736: informational records are excluded from the work-list so an
    # UNSPECIFIED field or a by-design absence cannot read as a defect.
    mism = [r for r in recs if r["class"] not in NON_DEFECT_CLASSES]
    info = [r for r in recs if r["class"] in NON_DEFECT_CLASSES]
    hits = []
    if do_ablate and post_usable and not match:
        hits = ablate(pre, post, guest, max_k=3)

    # primary class for clustering: first hard mismatch, else ablation, else root_only
    primary_class = "root_match" if match else "root_mismatch_unlocalized"
    primary_account = ""
    primary_field = ""
    if mism:
        primary_class = mism[0]["class"]
        primary_account = mism[0]["account"]
        primary_field = mism[0]["field"]
    elif hits and hits[0][0]:
        primary_class = f"ablate_{hits[0][1]}"
        primary_account = str(hits[0][0])[:40]
        primary_field = str(hits[0][1])

    return {
        "id": prefix,
        "label": label,
        "case": (case_key or "").split("::")[-1][:100],
        "block": bi,
        "nblocks": nblocks,
        "post_usable": int(post_usable),
        "exp_succ": exp_succ,
        "succ": succ,
        "bv": bv,
        "rc": rc,
        "post_root": post_root,
        "hdr_state_root": hdr,
        "guest_root": guest.hex(),  # sv_recomputed — cite #11547, not out[0:32]
        "match": int(match),
        "aw_count": len(aw_rows),
        "n_field_recs": len(mism),
        # GH #11736: a single `primary_*` triple reads as a complete answer. On
        # #11306 it surfaced only the sender and hid the coinbase leaf, and the
        # hidden leaf was the corroborating datum that turned a single-quantity
        # match into a three-way consistency check. These three fields make a
        # second leaf visible without anyone re-deriving the leaf set by hand.
        # `n_field_recs` does NOT answer this: it mixes field classes.
        "n_diverging_leaves": len({r["account"] for r in mism}),
        "diverging_accounts": ",".join(sorted({r["account"] for r in mism})),
        "diverging_by_field": ";".join(
            f"{f}={n}" for f, n in sorted(Counter(r["field"] for r in mism).items())
        ),
        "n_informational": len(info),
        "primary_class": primary_class,
        "primary_account": primary_account,
        "primary_field": primary_field,
        "field_recs": mism,
        "ablate_hits": [
            {"account": h[0], "field": h[1], "post": h[2], "alt": h[3]} for h in hits[:8]
        ],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--manifest", default=os.environ.get("MANIFEST", DEFAULT_MANIFEST))
    ap.add_argument(
        "--fixtures",
        default=os.environ.get("EEST_FIXTURES_DIR", str(DEFAULT_FXROOT)),
    )
    ap.add_argument("--ids", default="", help="comma-separated id prefixes")
    ap.add_argument("--fr-list", default="", help="file of labels/ids (e.g. fr_bv1.ids)")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--out", default="", help="TSV summary path")
    ap.add_argument("--jsonl", default="", help="full per-row JSONL path")
    ap.add_argument("--work", default="/tmp/opencode/leaf-decoder")
    ap.add_argument("--no-ablate", action="store_true")
    ap.add_argument("--cluster", action="store_true", help="print class×field cluster counts")
    args = ap.parse_args()

    fxroot = Path(args.fixtures)
    if not fxroot.is_dir():
        print(f"error: fixtures root missing: {fxroot}", file=sys.stderr)
        return 2
    if not os.path.isfile(args.elf):
        print(f"error: elf missing: {args.elf}", file=sys.stderr)
        return 2

    syms = nm_syms(args.elf)
    manifest_rows = load_manifest(args.manifest)
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)

    ids: list[str] = []
    if args.ids:
        ids.extend([x.strip() for x in args.ids.split(",") if x.strip()])
    if args.fr_list:
        with open(args.fr_list) as f:
            for line in f:
                lab = line.strip()
                if not lab:
                    continue
                # prefer 5-digit numeric prefix when present
                ids.append(lab[:5] if lab[:5].isdigit() else lab.split("_")[0])
    # dedupe preserving order
    seen: set[str] = set()
    uniq = []
    for i in ids:
        if i not in seen:
            seen.add(i)
            uniq.append(i)
    ids = uniq
    if args.limit:
        ids = ids[: args.limit]
    if not ids:
        print("error: no ids", file=sys.stderr)
        return 2

    results = []
    for i, prefix in enumerate(ids):
        print(f"[{i+1}/{len(ids)}] {prefix} …", flush=True)
        r = decode_one(
            prefix, manifest_rows, args.elf, fxroot, syms, work, do_ablate=not args.no_ablate
        )
        results.append(r)
        status = r.get("err") or (
            "MATCH" if r.get("match") else f"{r.get('primary_class')}:{r.get('primary_field')}"
        )
        print(
            f"  succ={r.get('succ')} bv={r.get('bv')} match={r.get('match')} "
            f"aw={r.get('aw_count')} → {status}",
            flush=True,
        )

    if args.jsonl:
        with open(args.jsonl, "w") as f:
            for r in results:
                f.write(json.dumps(r) + "\n")
        print(f"wrote {args.jsonl}")

    if args.out:
        # GH #11736: the four new columns are APPENDED, never inserted, so every
        # existing column keeps its index and a reader using `cut -f N` against an
        # older report is unaffected. See the PR body: the CLASS NAMES did change
        # for three previously-misreported cases, so class strings must not be
        # compared across the fix boundary even though the column layout is stable.
        fields = [
            "id", "succ", "bv", "match", "exp_succ", "block", "nblocks", "post_usable",
            "primary_class", "primary_field", "primary_account",
            "n_field_recs", "aw_count", "guest_root", "post_root", "label",
            "n_diverging_leaves", "diverging_accounts", "diverging_by_field",
            "n_informational",
        ]
        with open(args.out, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fields, delimiter="\t", extrasaction="ignore")
            w.writeheader()
            for r in results:
                w.writerow(r)
        print(f"wrote {args.out}")

    if args.cluster or True:
        c = Counter()
        for r in results:
            if r.get("err"):
                c[("ERR:" + r["err"], "", "")] += 1
            elif r.get("match"):
                c[("root_match", "", "")] += 1
            else:
                key = (r.get("primary_class") or "?", r.get("primary_field") or "", "")
                c[key] += 1
                # also count every field rec
                for fr in r.get("field_recs") or []:
                    c[(fr["class"], fr["field"], "detail")] += 1
        print("\n# cluster (primary row → count)")
        for (cls, field, kind), n in c.most_common():
            if kind == "detail":
                continue
            print(f"  {n:4d}  {cls:40s}  field={field}")
        print("\n# field-record detail counts (multi per row)")
        for (cls, field, kind), n in c.most_common():
            if kind != "detail":
                continue
            print(f"  {n:4d}  {cls:40s}  field={field}")

    n_match = sum(1 for r in results if r.get("match"))
    n_err = sum(1 for r in results if r.get("err"))
    n_mis = len(results) - n_match - n_err
    print(f"\n# summary: n={len(results)} match={n_match} mismatch={n_mis} err={n_err}")
    # GH #11736: make a hidden second leaf impossible to miss from the summary
    # alone. `primary_*` names ONE account; on #11306 every failing row had two,
    # and the second was the corroborating datum.
    multi = [r for r in results if (r.get("n_diverging_leaves") or 0) > 1]
    if multi:
        dist = Counter(r["n_diverging_leaves"] for r in multi)
        print(
            "# ⚠ MULTI-LEAF: "
            + f"{len(multi)} of {len(results)} row(s) diverge on MORE THAN ONE account "
            + "(" + ", ".join(f"{n} leaves×{c}" for n, c in sorted(dist.items())) + "). "
            + "primary_* names only the first -- read diverging_accounts."
        )
    n_info = sum(r.get("n_informational") or 0 for r in results)
    if n_info:
        print(
            f"# {n_info} informational record(s) excluded from the work-list "
            "(UNSPECIFIED fields, touched-only enumeration rows, storage handled in "
            "a separate structure) -- these are NOT defects, see GH #11736"
        )
    print("# note: guest_root is sv_recomputed (#11547), never out[0:32]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
