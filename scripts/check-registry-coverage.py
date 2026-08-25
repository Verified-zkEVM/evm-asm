#!/usr/bin/env python3
"""Fail when a linked, spec-bearing guest routine has NO row in either registry (GH #11637).

WHY THIS GATE EXISTS. Both proof registries already gate row *contents* — a row must
name a witnessed theorem (`gen-axiom-witnesses.py`), a verdict needs a spec
(`verdict_requires_spec`), a witnessed routine must not be `.unproven`
(`crossVerdictOk`). Every one of those quantifies over rows that EXIST. Nothing
gated row *existence*, so a routine could be linked into the guest, carry a
`sorry`-free whole-routine triple, and appear in neither registry — counting toward
nothing. #11342 found one instance; #11348 found another (`bloom_or_into`), and the
sweep behind #11637 found ~103. Proven work no census can see is indistinguishable
from work not done.

WHAT IT CHECKS. Recomputes four sets from source on every run:

  1. linked symbols          -- `def <sym> : Nat := 0x…` in Codegen/GuestAddrs.lean
  2. rowed routines          -- Progress/Routines.lean `routine "<sym>"`
  2b. corresponded routines  -- Progress/Correspondence.lean `routine := "<sym>"`
  3. routine-level specs     -- `theorem <name>{Fn_spec,Flat_spec,_spec_within,
                                _spec_within_<case>,_spec_pinned_within,
                                _spec_specref,_spec_ported,Spec_<case>}` anywhere
                                under EvmAsm/, mapped to a symbol by camel->snake
                                on the name minus that suffix

A symbol in (1) ∩ (3) but not in (2) must carry an allowlist entry naming a reason.

⚠️ (2) AND (2b) ARE DIFFERENT OBLIGATIONS AND ARE NOT UNIONED (GH #12526). This gate
originally required a row in *either* registry, which meant a correspondence row alone
satisfied it. But:

  * `Progress/Routines.lean`       asserts there is a MACHINE TRIPLE at a proof tier,
                                   anchored at the guest address.
  * `Progress/Correspondence.lean` asserts the routine's SPEC AGREES WITH THE REFERENCE
                                   (execution-specs, via SpecRef).

Neither implies the other: a routine can be spec-corresponded with no machine triple at
all. Under the union, such a routine was reported `registered`, never entered the backlog,
and never needed an allowlist entry stating a reason — so the count silently mixed two
claims. This gate now measures the machine-triple obligation ONLY, and reports the
correspondence-only set as a separate census line so it is visible rather than absorbed.
When #12526 was fixed, exactly 2 linked spec-bearing symbols moved from invisible to
tracked: `rlp_content_to_u256_be_strict` and `rlp_content_to_u64_strict`. Neither was
rowable anyway, so live exposure was NIL — the defect was that the gate accepted them for
the WRONG REASON (it believed they were registered, rather than knowing they were not yet
rowable). ⚠️ And the reason is not the one `--shape` alone suggests: it grades both
`structured-only`, but READING them shows each IS a whole-routine flat `cpsTripleWithin`
— at a FREE `base`, over `rlp_content_to_*_code base`. So the remedy is instantiation at
`GuestAddrs.<sym>` plus a `guestImageEntries` pairing (neither symbol has one), the
`u256_eq`/`eip8037_tx_state_gas` class — NOT `Fn.retSpecFlat`. Their allowlist entries
record that, because a coverage backlog whose stated remedy is wrong sends the next
person down the wrong path.

The gate also runs a loose `spec`/`Spec` tree scan over linked-symbol prefixes.
Any declaration that scan finds but `SPEC_RE` misses is a naming-convention
failure, except for explicitly documented non-routine false positives.

⚠️ THE MAPPING IS NAME-BASED, and deliberately so: it needs no build and no
elaboration, which is what makes it cheap enough to run every time. The cost is that
a theorem whose name happens to match a symbol while proving something narrower
reads as covered. That is the right failure direction for a *coverage* gate — it can
under-report a gap, never invent one — but it means this gate is a floor on the
backlog, not a census. `EvmAsm/Progress/**` is excluded from the scan so the
registries' own witness abbrevs and docstrings do not count as specs.

⚠️ THE MAPPING IS NAME-BASED PLUS ONE NAMESPACE RULE (GH #12568). Purely name-based
was not enough: a routine's contract need not be named after the whole symbol.
`pointDouble_spec` proves the whole-routine triple for `secp256k1_point_double`, with
`Secp256k1` supplied by the enclosing namespace rather than by the theorem name. The
name-only mapping resolved that to `point_double`, which is not a linked symbol, and
the lookup then DROPPED IT SILENTLY — so a complete, image-anchored triple was
invisible while this gate printed OK. That is the `_fnspec` class again, reappearing
through a namespace-carries-the-prefix convention.

`namespace_attributed` recovers those, under a deliberately narrow rule: the stripped
name must be a `_`-boundary SUFFIX of a linked symbol that the SAME FILE cites as
`GuestAddrs.<symbol>`. Both conjuncts are load-bearing (the self-test checks that),
because the suffix alone would attach short helper names to arbitrary routines — which
would INVENT gaps, the one failure direction this gate must not have.
`NAMESPACE_ATTRIB_ALLOW` holds the case lemmas that resolve by the rule but are not
contracts; it must stay tiny, since a long list means the rule is too loose. Every
recovery is PRINTED, not merely counted.

Measured when the rule landed: of 3333 `SPEC_RE` matches whose stripped name is not a
linked symbol, only 3 were namespace-prefix candidates — two already rowed
(`mpt_resolve_cache_reset`, `node_db_lookup`) and `secp256k1_point_double`, the single
symbol where the blind spot concealed real unrowed work.

THE ALLOWLIST EXPIRES, which is the whole ratchet (same shape as
routine-liveness-allow.txt, GH #11303/#11332). An entry is STALE — and fails the run,
naming the line to delete — once the symbol gains a row, loses its spec, or leaves
the guest image. So the backlog burns down visibly instead of silently, and a NEW
gap fails immediately rather than joining a pile nobody reads.

TIERS are reported because the remedies differ:
  * A -- a flat `cpsTripleWithin` at the guest address (the file names
    `GuestAddrs.<sym>`): registrable as `.proven` today, no new proof work.
  * B -- a structured SAsm `.Spec` only: needs `Fn.retSpecFlat` first, so a
    `.proven` row would overclaim. Do NOT bulk-register these.
"""
from __future__ import annotations

import collections
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
GUEST_ADDRS = REPO / "EvmAsm" / "Codegen" / "GuestAddrs.lean"
ROUTINES = REPO / "EvmAsm" / "Progress" / "Routines.lean"
CORRESPOND = REPO / "EvmAsm" / "Progress" / "Correspondence.lean"
ALLOW = REPO / "scripts" / "registry-coverage-allow.txt"

# `_fnspec` is listed FIRST and is not redundant with `_spec`: in `…_fnspec` the
# substring "spec" is preceded by "n", not "_", so `_spec` cannot match it. Before
# it was added, the three `_fnspec` header byte-field extractors
# (`header_extract_state_root`, `_receipts_root`, `_withdrawals_root`) were LINKED,
# carried whole-routine `cpsTripleWithin`s, and were in neither registry nor the
# allowlist — and this gate scanned straight past them, reporting nothing. That is
# the #11042 silent-skip class the gate exists to prevent, reappearing through a
# naming convention the pattern did not cover. A census that cannot see a
# convention is indistinguishable from one that finds nothing wrong.
SPEC_SUFFIXES = (
    "_spec_within_empty_section",
    "_spec_within_empty_len",
    "_spec_within_enabled_empty",
    "_spec_within_nonempty",
    "_spec_within_short",
    "_spec_within_empty",
    "_spec_within_one_hit",
    "_spec_pinned_within",
    "_spec_specref",
    "_specRef_correspondence",
    "_spec_ported",
    "_fnspec",
    "Fn_spec",
    "Flat_spec_domain",
    "Flat_spec",
    "_spec_within",
    "_spec",
)
SPEC_SUFFIX_PATTERN = "|".join(re.escape(suf) for suf in SPEC_SUFFIXES)
SPEC_GENERIC_SUFFIX_PATTERN = (
    r"_spec_within_[A-Za-z0-9_]+|Flat_spec_[A-Za-z0-9_]+|Spec_[A-Za-z0-9_]+"
)
SPEC_NAME_SUFFIX_PATTERN = (
    r"(?:" + SPEC_SUFFIX_PATTERN + r"|" + SPEC_GENERIC_SUFFIX_PATTERN + r")"
)
SPEC_RE = re.compile(
    r"^\s*theorem\s+(\w+?" + SPEC_NAME_SUFFIX_PATTERN + r")\b",
    re.M,
)
SPEC_GENERIC_SUFFIX_RE = re.compile(
    r"(?:_spec_within_[A-Za-z0-9_]+|Flat_spec_[A-Za-z0-9_]+|Spec_[A-Za-z0-9_]+)$"
)

# The suffixes that (together with a `GuestAddrs.<sym>` citation in the same file)
# are this gate's tier-A proxy for "the theorem is a WHOLE-ROUTINE contract" rather
# than a case lemma or one domain-restricted arm. The longer members of
# `SPEC_SUFFIXES` deliberately do NOT qualify: `_spec_within_empty_section`,
# `_spec_within_enabled_empty`, `_spec_within_short` name a DOMAIN, not the routine.
#
# ⚠️ A NAME proxy, not a statement read — see the tier note in the module docstring.
# Named rather than inlined because `scripts/callee-composition-queue.py` reuses it
# to demote a callee out of its `startable` bucket (#12318); a second copy of this
# tuple in that script would drift away from this one and quietly disagree.
WHOLE_ROUTINE_SPEC_SUFFIXES = ("_spec_within", "Flat_spec")


def is_whole_routine_spec_name(thm: str) -> bool:
    """Name-proxy: does this theorem name claim a whole-routine contract?

    ⚠️ Proxy only. It cannot see that `header_extended_decode_u64_segment_spec_within`
    is a per-field segment lemma, and it cannot see that the pre-convention
    `u256Eq_spec` IS a whole-routine triple. Sound only in the demoting direction.
    """
    return thm.endswith(WHOLE_ROUTINE_SPEC_SUFFIXES)


def camel_to_snake(s: str) -> str:
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", s)
    s = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", "_", s)
    return s.lower().strip("_")


def strip_spec_suffix(thm: str) -> str:
    for suf in SPEC_SUFFIXES:
        if thm.endswith(suf):
            return thm[: -len(suf)]
    generic = SPEC_GENERIC_SUFFIX_RE.search(thm)
    if generic:
        return thm[: generic.start()]
    return thm


def snake_to_camel(s: str) -> str:
    head, *tail = s.split("_")
    return head + "".join(part[:1].upper() + part[1:] for part in tail)


def linked_symbols() -> set[str]:
    return set(re.findall(r"^def ([a-z_0-9]+) : Nat := 0x", GUEST_ADDRS.read_text(), re.M))


def rowed() -> set[str]:
    """Symbols with a proof-tier row in Progress/Routines.lean — the machine-triple claim.

    This, NOT the union with Correspondence.lean, is what the coverage gate measures
    (#12526). See the module docstring for why the two registries cannot be pooled.
    """
    return set(re.findall(r'^  routine "([a-z_0-9]+)"', ROUTINES.read_text(), re.M))


def corresponded() -> set[str]:
    """Symbols with a row in Progress/Correspondence.lean — the spec-agreement claim.

    Reported as a separate census, and deliberately NOT accepted as machine-triple
    coverage.
    """
    return set(re.findall(r'routine := "([a-z_0-9]+)"', CORRESPOND.read_text()))


# Theorems that RESOLVE by the namespace rule below but are NOT routine-level
# contracts, so attributing them to a routine would invent a gap rather than find
# one. This gate's failure direction is deliberate — it may under-report a gap, it
# must never manufacture one — so each entry is a case lemma, not a contract.
# Same role as LOOSE_SPEC_ALLOW, and it must stay tiny: a long list here means the
# suffix rule below is too loose.
NAMESPACE_ATTRIB_ALLOW = {
    # `lookupSpec_none_snoc` is an induction step over the pure lookup spec, not a
    # machine contract for `node_db_lookup`.
    "lookupSpec_none_snoc",
}

# Populated by `spec_bearing`; reported so a namespace-recovered attribution is
# visible rather than merely counted.
NAMESPACE_RECOVERED: list[tuple[str, str, str, str]] = []


def namespace_attributed(thm: str, sym: str, txt: str, symbols: set[str]):
    """Recover a linked symbol when the theorem name DROPS a namespace-carried prefix.

    A routine's contract is not always named after the whole symbol: `pointDouble_spec`
    proves the whole-routine triple for `secp256k1_point_double`, with `Secp256k1`
    supplied by the enclosing namespace (`EvmAsm.Codegen.Secp256k1PointDoubleSAsm`)
    rather than by the theorem name. The name-only mapping resolves that to
    `point_double`, which is not a linked symbol, and the caller then dropped it
    SILENTLY — so a complete, image-anchored whole-routine triple was invisible to the
    census while this gate printed OK (GH #12568).

    Recovery rule, deliberately narrow: the stripped name must be a `_`-boundary
    SUFFIX of a linked symbol that THIS FILE cites as `GuestAddrs.<symbol>`. Both
    conjuncts matter — the suffix alone would match unrelated short names, and the
    citation is what ties the theorem to that routine's address.
    """
    if thm in NAMESPACE_ATTRIB_ALLOW:
        return None
    for cand in sorted(symbols):
        if cand != sym and cand.endswith("_" + sym) and f"GuestAddrs.{cand}" in txt:
            return cand
    return None


def spec_bearing(symbols: set[str]) -> dict[str, list[tuple[str, str, bool]]]:
    """symbol -> [(theorem, file, cites_guest_addr)]"""
    out: dict[str, list[tuple[str, str, bool]]] = collections.defaultdict(list)
    for f in sorted(REPO.glob("EvmAsm/**/*.lean")):
        rel = f.relative_to(REPO).as_posix()
        if rel.startswith("EvmAsm/Progress/"):
            continue
        try:
            txt = f.read_text()
        except OSError:
            continue
        if "theorem" not in txt:
            continue
        for thm in SPEC_RE.findall(txt):
            base = strip_spec_suffix(thm)
            sym = camel_to_snake(base)
            if sym in symbols:
                out[sym].append((thm, rel, f"GuestAddrs.{sym}" in txt))
                continue
            # #12568: the name-only mapping missed it. Before discarding, try the
            # namespace-carried prefix -- this is where a whole-routine triple used
            # to vanish without a trace.
            recovered = namespace_attributed(thm, sym, txt, symbols)
            if recovered is not None:
                out[recovered].append((thm, rel, True))
                NAMESPACE_RECOVERED.append((thm, rel, sym, recovered))
    return out


LOOSE_SPEC_RE = re.compile(
    r"^\s*theorem\s+([A-Za-z0-9_]*[sS][pP][eE][cC][A-Za-z0-9_]*)(?=\s|\()",
    re.M,
)


def linked_spec_declarations(symbols: set[str]) -> list[tuple[str, str]]:
    """Return loose spec-like theorem names that prefix a linked symbol.

    The linked-symbol prefix keeps the intentionally loose `spec` search from
    treating every helper lemma containing that substring as a routine-level
    naming convention. The first character after the prefix must be `_` or
    uppercase; known non-routine false positives are handled separately below.
    """
    variants = [(sym, {sym, snake_to_camel(sym)}) for sym in sorted(symbols)]
    out: list[tuple[str, str]] = []
    for f in sorted(REPO.glob("EvmAsm/**/*.lean")):
        rel = f.relative_to(REPO).as_posix()
        if rel.startswith("EvmAsm/Progress/"):
            continue
        try:
            txt = f.read_text()
        except OSError:
            continue
        for thm in LOOSE_SPEC_RE.findall(txt):
            for _, names in variants:
                if any(
                    thm.startswith(name)
                    and len(thm) > len(name)
                    and (thm[len(name)] == "_" or thm[len(name)].isupper())
                    for name in names
                ):
                    out.append((thm, rel))
                    break
    return out


LOOSE_SPEC_ALLOW = {
    "evmEnvLoadHandlerSpec": "evm_env is a data symbol, not this handler routine",
    # K74's `_specref_` layer is deliberately attribution, not another machine
    # contract for `header_validate_base_fee`.  The main theorem composes the
    # machine-layer wrapper with SpecRef outcomes; the remaining declarations
    # are its premise/post non-vacuity witnesses.  They must stay visible to
    # this scan without being mistaken for rowable routine specs.
    "header_validate_base_fee_specref_within":
        "K74 header_validate_base_fee SpecRef attribution; row after the machine contract and SpecRef correspondence are discharged",
    "header_validate_base_fee_specref_within_inhabitable":
        "K74 header_validate_base_fee SpecRef attribution premise witness; row after the enclosing machine contract is discharged",
    "header_validate_base_fee_specref_final_inhabited":
        "K74 header_validate_base_fee SpecRef final-state attribution witness; row after the enclosing machine contract is discharged",
    "header_validate_base_fee_specref_within_arm0_inhabitable":
        "K74 header_validate_base_fee SpecRef arm-0 attribution witness; row after the enclosing machine contract is discharged",
    "header_validate_base_fee_specref_within_arm1_inhabitable":
        "K74 header_validate_base_fee SpecRef arm-1 attribution witness; row after the enclosing machine contract is discharged",
    "header_validate_base_fee_specref_within_arm2_inhabitable":
        "K74 header_validate_base_fee SpecRef arm-2 attribution witness; row after the enclosing machine contract is discharged",
    "header_validate_base_fee_specref_within_arm0_yields_post":
        "K74 header_validate_base_fee SpecRef arm-0 post attribution witness; row after the enclosing machine contract is discharged",
    "header_validate_base_fee_specref_within_arm1_yields_post":
        "K74 header_validate_base_fee SpecRef arm-1 post attribution witness; row after the enclosing machine contract is discharged",
    "header_validate_base_fee_specref_within_arm2_yields_post":
        "K74 header_validate_base_fee SpecRef arm-2 post attribution witness; row after the enclosing machine contract is discharged",
}


def loose_spec_misses(tree_specs: list[tuple[str, str]]) -> list[tuple[str, str]]:
    return [
        (thm, rel)
        for thm, rel in tree_specs
        if thm not in LOOSE_SPEC_ALLOW and not SPEC_RE.search("theorem " + thm)
    ]


def read_allow() -> dict[str, str]:
    entries: dict[str, str] = {}
    if not ALLOW.is_file():
        return entries
    for line in ALLOW.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        sym, _, reason = line.partition("\t")
        entries[sym.strip()] = reason.strip()
    return entries


def main() -> int:
    symbols = linked_symbols()
    reg = rowed()
    corr = corresponded()
    specs = spec_bearing(symbols)
    allow = read_allow()
    tree_specs = linked_spec_declarations(symbols)
    tree_misses = loose_spec_misses(tree_specs)

    # #12526: measured against the ROWED set only. A correspondence row proves a
    # different thing and cannot discharge the machine-triple obligation.
    gaps = {s: v for s, v in specs.items() if s not in reg}
    # Census, not a gate: linked symbols carrying a correspondence row but no
    # proof-tier row. Printed so the distinction stays visible in the output.
    corr_only = sorted(s for s in (corr - reg) if s in symbols)
    corr_only_spec = [s for s in corr_only if s in specs]
    tier_a = {s: v for s, v in gaps.items()
              if any(cites and is_whole_routine_spec_name(thm)
                     for thm, _, cites in v)}

    # NEW gaps -- not allowlisted. These fail.
    new = sorted(set(gaps) - set(allow))
    # STALE entries -- allowlisted but no longer a gap. These fail too (the ratchet).
    stale: list[tuple[str, str]] = []
    for sym in sorted(allow):
        if sym not in symbols:
            stale.append((sym, "no longer a linked guest symbol"))
        elif sym in reg:
            stale.append((sym, "now rowed in Progress/Routines.lean -- delete this line"))
        elif sym not in specs:
            stale.append((sym, "no longer has a routine-level spec theorem"))

    print(f"check-registry-coverage: {len(symbols)} linked symbols, {len(reg)} rowed "
          f"(Progress/Routines.lean), {len(specs)} spec-bearing, {len(gaps)} uncovered "
          f"({len(tier_a)} tier-A, {len(gaps) - len(tier_a)} tier-B), "
          f"{len(allow)} allowlisted")
    print(f"check-registry-coverage: {len(corr)} corresponded "
          f"(Progress/Correspondence.lean), of which {len(corr_only)} linked symbol(s) have "
          f"NO proof-tier row ({len(corr_only_spec)} spec-bearing, so gated above) — "
          "a correspondence row is spec agreement, NOT a machine triple (#12526)")
    print(f"check-registry-coverage: spec-name tree scan checked {len(tree_specs)} "
          f"linked declarations ({len(LOOSE_SPEC_ALLOW)} known non-routine exception)")
    if NAMESPACE_RECOVERED:
        print(f"check-registry-coverage: {len(NAMESPACE_RECOVERED)} attribution(s) "
              f"recovered via the enclosing NAMESPACE (theorem name drops a prefix the "
              f"namespace carries; these used to be dropped silently, #12568) — "
              f"{len(NAMESPACE_ATTRIB_ALLOW)} known non-contract exception(s)")
        for thm, rel, named, real in NAMESPACE_RECOVERED:
            print(f"    {thm}\t{named} -> {real}\t{rel}")

    if new:
        print(f"\ncheck-registry-coverage: FAIL — {len(new)} linked, spec-bearing "
              f"routine(s) have NO proof-tier row in Progress/Routines.lean and no "
              f"allowlist entry:",
              file=sys.stderr)
        for sym in new:
            thm, rel, cites = specs[sym][0]
            tier = "A" if sym in tier_a else "B"
            print(f"    [{tier}] {sym}\t{thm}\t{rel}", file=sys.stderr)
        print("\n  Add a row to EvmAsm/Progress/Routines.lean (tier A: a flat triple at the\n"
              "  guest address is registrable as `.proven` today) or, if the spec is a\n"
              "  structured SAsm `.Spec` only (tier B), either derive the flat triple with\n"
              "  `Fn.retSpecFlat` first or add an allowlist entry in\n"
              "  scripts/registry-coverage-allow.txt saying why it is not registered yet.\n"
              "  ⚠️ Do NOT grade a structured-only spec `.proven` to silence this — that is\n"
              "  the invisible overclaim #11637 exists to stop.\n"
              "  ⚠️ A row in Progress/Correspondence.lean does NOT satisfy this gate: spec\n"
              "  agreement with the reference is a different obligation from a machine\n"
              "  triple at the guest address (#12526).", file=sys.stderr)

    if stale:
        print(f"\ncheck-registry-coverage: FAIL — {len(stale)} STALE allowlist entr(ies) in "
              f"{ALLOW.relative_to(REPO)}:", file=sys.stderr)
        for sym, why in stale:
            print(f"    {sym}\t{why}", file=sys.stderr)
        print("\n  Delete them. The allowlist expires on purpose: an exemption that outlives\n"
              "  its reason is how a backlog goes silent again.", file=sys.stderr)

    if tree_misses:
        print("\ncheck-registry-coverage: FAIL — loose spec-name scan found theorem "
              "declarations that SPEC_RE does not recognise:", file=sys.stderr)
        for thm, rel in tree_misses:
            print(f"    {thm}\t{rel}", file=sys.stderr)
        print("\n  Add the naming convention to SPEC_RE and its suffix-stripping logic, "
              "or add a narrowly justified non-routine exception.", file=sys.stderr)

    if new or stale or tree_misses:
        return 1
    print("check-registry-coverage: OK — every linked, spec-bearing routine either has a "
          "proof-tier row in Progress/Routines.lean or is allowlisted with a reason.")
    return 0


def self_test() -> int:
    """Assert `SPEC_RE` recognises every spec-theorem naming convention in the tree.

    A census that cannot see a convention reports nothing wrong, which is
    indistinguishable from finding nothing wrong. `_fnspec` was exactly that: three
    linked, spec-bearing header extractors were invisible to this gate, so it passed
    while covering none of them. The normal gate and this self-test both run a loose
    linked-symbol tree scan, while the synthetic names below provide a cheap stable
    regression net for suffix stripping.
    """
    must_match = [
        ("theorem header_extract_state_root_fnspec", "header_extract_state_root_fnspec"),
        ("theorem reb_spec_within", "reb_spec_within"),
        ("theorem bgvU32leFlat_spec", "bgvU32leFlat_spec"),
        ("theorem bahU32leFn_spec", "bahU32leFn_spec"),
        ("theorem rlpListNthItem_spec", "rlpListNthItem_spec"),
        ("theorem erh_hash_one_spec_within_empty", "erh_hash_one_spec_within_empty"),
        ("theorem erh_hash_one_spec_within_nonempty", "erh_hash_one_spec_within_nonempty"),
        ("theorem witness_codes_lookup_by_hash_spec_within_empty_section",
         "witness_codes_lookup_by_hash_spec_within_empty_section"),
        ("theorem witness_lookup_by_hash_indexed_spec_within_one_hit",
         "witness_lookup_by_hash_indexed_spec_within_one_hit"),
        ("theorem witness_lookup_by_hash_indexed_spec_within_empty_len",
         "witness_lookup_by_hash_indexed_spec_within_empty_len"),
        ("theorem mset_memcpy_spec_pinned_within", "mset_memcpy_spec_pinned_within"),
        ("theorem blsgLtP_spec_specref", "blsgLtP_spec_specref"),
        ("theorem hp_decode_nibbles_spec_ported", "hp_decode_nibbles_spec_ported"),
        ("theorem tx_signing_hash_specRef_correspondence",
         "tx_signing_hash_specRef_correspondence"),
        ("theorem mptNodeKindSpec_rlp", "mptNodeKindSpec_rlp"),
    ]
    failures: list[str] = []
    for src, want in must_match:
        got = SPEC_RE.findall(src)
        if want not in got:
            failures.append(f"SPEC_RE missed {want!r} (matched {got!r})")

    # Suffix stripping must recover the guest symbol, or the theorem is attributed
    # to the wrong routine (or to none) even once the pattern matches.
    for thm, want_sym in [("header_extract_state_root_fnspec", "header_extract_state_root"),
                          ("reb_spec_within", "reb"),
                          ("bgvU32leFlat_spec", "bgv_u32le"),
                          ("erh_hash_one_spec_within_empty", "erh_hash_one"),
                          ("mset_memcpy_spec_pinned_within", "mset_memcpy"),
                          ("blsgLtP_spec_specref", "blsg_lt_p"),
                          ("hp_decode_nibbles_spec_ported", "hp_decode_nibbles"),
                          ("tx_signing_hash_specRef_correspondence", "tx_signing_hash"),
                          ("mptNodeKindSpec_rlp", "mpt_node_kind")]:
        base = strip_spec_suffix(thm)
        if camel_to_snake(base) != want_sym:
            failures.append(
                f"suffix strip of {thm!r} gave {camel_to_snake(base)!r}, want {want_sym!r}")

    # A name that merely CONTAINS "spec" must not match, or the census inflates.
    for src in ["theorem inspection_helper", "theorem specialised_thing"]:
        if SPEC_RE.findall(src):
            failures.append(f"SPEC_RE over-matched on {src!r}")

    tree_specs = linked_spec_declarations(linked_symbols())
    for thm, rel in loose_spec_misses(tree_specs):
        failures.append(f"tree scan: SPEC_RE missed {thm!r} in {rel}")

    # #12526 REGRESSION NET, with a negative control. The defect being pinned here is
    # that pooling the two registries let a correspondence row discharge the
    # machine-triple obligation. A test that only asserts "the gate passes" cannot see
    # that come back, because the gate passed *before* the fix too. So assert instead
    # that the distinction is LIVE and that the correspondence-only set is genuinely
    # NOT treated as coverage.
    symbols_st = linked_symbols()
    reg_st, corr_st = rowed(), corresponded()
    specs_st = spec_bearing(symbols_st)
    allow_st = read_allow()

    # (a) Non-vacuity: if the two registries ever coincided, this test would pass for
    #     the wrong reason -- there would be no correspondence-only symbol to misjudge.
    corr_only_st = sorted(s for s in (corr_st - reg_st) if s in symbols_st)
    if not corr_only_st:
        failures.append(
            "#12526 net is vacuous: no linked correspondence-only symbol exists, so "
            "'a correspondence row is not coverage' is untested -- re-point this net")

    # (b) The control itself: under the OLD union rule each of these would count as
    #     `registered` and vanish from the backlog. Under the fixed rule each must be
    #     accounted for explicitly -- reported as a gap or carrying an allowlist reason.
    for sym in corr_only_st:
        if sym in reg_st:
            failures.append(f"#12526: {sym} classified rowed while absent from Routines.lean")
        if sym in specs_st and sym not in allow_st:
            failures.append(
                f"#12526: {sym} is linked, spec-bearing and correspondence-only, but is "
                "neither allowlisted nor reported -- the union defect is back")

    # #12568 REGRESSION NET. The defect was a SILENT DROP: a theorem whose name maps
    # to no linked symbol was discarded, so a complete whole-routine triple for
    # `secp256k1_point_double` was invisible while the gate printed OK. "The gate is
    # green" cannot witness the fix -- it was green before it too.
    NS_specs = spec_bearing(symbols_st)

    # (a) The concrete case must now resolve, and to the RIGHT symbol.
    pd = [t for t, _, _ in NS_specs.get("secp256k1_point_double", [])]
    if "pointDouble_spec" not in pd:
        failures.append(
            "#12568: pointDouble_spec no longer attributes to secp256k1_point_double "
            f"(got {pd!r}) -- the namespace recovery regressed")

    # (b) Non-vacuity: if nothing were ever recovered, the rule would be untested and
    #     (a) could pass for an unrelated reason.
    if not NAMESPACE_RECOVERED:
        failures.append(
            "#12568 net is vacuous: no attribution was recovered via the namespace, so "
            "the rule is untested -- re-point this net")

    # (c) Failure DIRECTION: the exception list must actually suppress. This gate may
    #     under-report a gap but must never manufacture one, so a case lemma that
    #     merely resolves by suffix must NOT be attributed to a routine.
    for thm in NAMESPACE_ATTRIB_ALLOW:
        if any(t == thm for lst in NS_specs.values() for t, _, _ in lst):
            failures.append(
                f"#12568: {thm} is in NAMESPACE_ATTRIB_ALLOW but was still attributed "
                "to a routine -- the exception list is not being honoured")
        if namespace_attributed(thm, "ignored", "GuestAddrs.anything", symbols_st) is not None:
            failures.append(f"#12568: namespace_attributed ignores the allow list for {thm}")

    # (d) Both conjuncts of the narrow rule must be load-bearing. A `_`-boundary suffix
    #     with NO GuestAddrs citation in the file must not resolve, or the rule would
    #     start attaching short helper names to arbitrary routines.
    suffix_only = namespace_attributed("someThing_spec", "double",
                                       "no citation here", symbols_st)
    if suffix_only is not None:
        failures.append(
            f"#12568: suffix match resolved to {suffix_only!r} with no GuestAddrs "
            "citation -- the citation conjunct is not load-bearing")

    # (c) `rowed()` must not read Correspondence.lean at all. A symbol rowed ONLY there
    #     is the exact input that used to be misclassified.
    corr_text_syms = set(re.findall(r'routine := "([a-z_0-9]+)"', CORRESPOND.read_text()))
    routines_text_syms = set(
        re.findall(r'^  routine "([a-z_0-9]+)"', ROUTINES.read_text(), re.M))
    if rowed() != routines_text_syms:
        failures.append("#12526: rowed() no longer equals the Routines.lean row set")
    if corresponded() != corr_text_syms:
        failures.append("#12526: corresponded() no longer equals the Correspondence.lean set")

    if failures:
        print("check-registry-coverage --self-test: FAIL", file=sys.stderr)
        for f in failures:
            print(f"    {f}", file=sys.stderr)
        return 1
    print(f"check-registry-coverage --self-test: OK — {len(must_match)} naming "
          "convention(s) recognised, suffix stripping recovers the symbol, "
          f"no over-match; tree scan checked {len(tree_specs)} linked declarations "
          f"({len(LOOSE_SPEC_ALLOW)} known non-routine exception).")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main())
