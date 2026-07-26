#!/usr/bin/env python3
"""Analyze semantic-boundary-v2 diagnostic output without raw-delta IDs."""

import argparse
import csv
import json
from collections import Counter, defaultdict


def number(row, key):
    value = row[key]
    return 0 if value == "" else int(value)


def delta_bucket(value):
    magnitude = abs(value)
    if magnitude == 0:
        return "zero"
    if magnitude <= 1024:
        return f"small:{magnitude}"
    if magnitude <= 1_000_000:
        return "medium"
    return "large"


def relation(row):
    header = number(row, "u64_120")
    maximum = number(row, "u64_128")
    tx_count = number(row, "u64_144")
    regular = number(row, "u64_152")
    state = number(row, "u64_160")
    before = number(row, "u64_168")
    first_limit = number(row, "u64_176")
    arena_status = number(row, "u64_184")
    arena_index = number(row, "u64_192")
    runtime_count = number(row, "u64_208")
    eip_status = number(row, "u64_216")
    eip_index = number(row, "u64_224")
    auth_success = number(row, "u64_232")
    rolled_back = number(row, "u64_240")
    mtx_i = number(row, "u64_248")
    fail_code = number(row, "u64_112")
    # Header gas_used is nonzero for this tx-bearing diagnostic population.
    # A zero header+expected pair therefore means ExactGas never wrote it, not
    # a computed zero. Undefined fields must not shape root identities.
    settlement_reached = header != 0 or maximum != 0
    first_index = f"arena:{arena_index}" if arena_index else (
        f"eip:{eip_index}" if eip_index else "NONE"
    )
    mask = {
        "tx": "one" if tx_count == 1 else "many",
        "settlement": "reached" if settlement_reached else f"early:code{fail_code}",
    }
    if not settlement_reached:
        return mask, {"gas": "UNWRITTEN"}, {}
    mask.update({
        "H=before": header == before,
        "H=first_limit": header == first_limit,
        "H=max": header == maximum,
        "max=state": maximum == state,
        "max=regular": maximum == regular,
        "before=regular+state": before == regular + state,
        "state_zero": state == 0,
        "regular_zero": regular == 0,
        "arena_ok": arena_status == 0,
        "runtime_complete": runtime_count == tx_count,
        "eip7778_ok": eip_status == 0,
        "auth_success_nonzero": auth_success != 0,
        "rolled_back": rolled_back != 0,
        "mtx_i_eq_tx_count": mtx_i == tx_count,
        "first_index": first_index,
    })
    raw = {
        "d_Hmax": header - maximum,
        "d_before_sum": before - regular - state,
        "d_limit_header": first_limit - header,
        "before_minus_state_regular": before - state - regular,
    }
    return mask, {name: delta_bucket(value) for name, value in raw.items()}, raw


def root_id(mask, buckets):
    # Exact raw deltas never form identities; cardinality is reported separately.
    return tuple(mask.items()), tuple(buckets.items())


def compact(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"))


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tsv")
    parser.add_argument("--expected-rows", type=int, required=True)
    return parser.parse_args()


def main():
    args = parse_args()
    with open(args.tsv, newline="") as source:
        rows = list(csv.DictReader(
            (line for line in source if not line.startswith("#")), delimiter="\t"))
    assert len(rows) == args.expected_rows, (
        f"selected denominator {len(rows)} != {args.expected_rows}")
    assert len({row["label"] for row in rows}) == len(rows), "labels are not unique"
    frs = [row for row in rows if row["cat"] == "FR"]
    print(f"denominator={len(rows)} FR={len(frs)} "
          f"categories={dict(sorted(Counter(row['cat'] for row in rows).items()))}")

    groups = defaultdict(list)
    row_relation = {}
    for row in rows:
        mask, buckets, raw = relation(row)
        key = root_id(mask, buckets)
        if row["cat"] == "FR":
            groups[key].append((row, mask, buckets, raw))
        row_relation[row["label"]] = (key, mask, buckets, raw)

    sizes = Counter(map(len, groups.values()))
    print(f"roots={len(groups)} largest={max(map(len, groups.values()), default=0)} "
          f"singletons={sizes[1]} size_distribution={dict(sorted(sizes.items()))}")
    ranked = sorted(groups.items(), key=lambda item: (-len(item[1]), item[1][0][0]["label"]))
    for ordinal, (_, entries) in enumerate(ranked, 1):
        rows_here = [entry[0] for entry in entries]
        cardinalities = {
            name: len({entry[3][name] for entry in entries}) for name in entries[0][3]
        }
        codes = dict(sorted(Counter(number(row, "u64_112") for row in rows_here).items()))
        reps = ",".join(row["label"] for row in rows_here[:6])
        print(f"ROOT {ordinal} count={len(entries)} reps={reps} codes={codes} "
              f"mask={compact(entries[0][1])} buckets={compact(entries[0][2])} "
              f"raw_cardinality={compact(cardinalities)}")


if __name__ == "__main__":
    main()
