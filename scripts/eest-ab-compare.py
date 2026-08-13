#!/usr/bin/env python3
"""Compare two `codegen-eest-stateless-check` run dirs — with self-checks.

    scripts/eest-ab-compare.py BASE_RUN_DIR CANDIDATE_RUN_DIR

Reports the FA/FR delta between a base run and a candidate run, where FA/FR are
judged on the SUCC BIT (byte 32 of the guest output) against each manifest's
recorded expectation:

    guest succ=1, expected succ=0  ->  FALSE ACCEPT  (inviolable: must stay 0)
    guest succ=0, expected succ=1  ->  FALSE REJECT  (allowed; fewer is better)

Byte-identity is checked against the full captured output window (bytes 0..255)
from each successful case's `.output` file. The `.result.tsv` field remains the
fixture-sized projection used for FA/FR classification; it is not sufficient for
the equivalence check because normal Amsterdam fixtures project only 105 bytes.

WHY THIS EXISTS
---------------
Three ways an A/B number silently becomes meaningless, all hit in practice:

1. TRUNCATED ENUMERATION.  `ls DIR/*.result.tsv` exceeds ARG_MAX on a
   full-corpus run dir (72k+ files), so the counter reports 0 — which reads as a
   clean sweep rather than a broken instrument.  See #10536 / #10538.  This
   script enumerates with `os.scandir`, in-process, so there is no argv limit.

2. SHORT DENOMINATOR.  An `FA=0` computed over a subset of the manifest is not
   `FA=0`.  Asserted below: each side must have scored every manifest row (a
   candidate may be a deliberate `--limit` sample; the BASE may not).

3. LOSSY JOIN.  This is the subtle one.  Matching two runs on a label or a
   fixture path silently collapses rows via key collisions — measured on a real
   corpus: joining on the label minus its run-order prefix mapped 600 rows to
   368, and joining on fixture relpath mapped them to 166.  Either reports
   "byte-identical" over a 28-61% denominator while looking like a clean pass.

   No manifest field can join two runs: only the label is unique
   (26104/26104), and it carries a run-ORDER prefix, so a shuffled `--random`
   run does not share it.  Every content field collides — stripped label 15050,
   relpath 3149, expected-hex 21476, and pair-keys 22285/23014 out of 26104.

   So the join key here is the SHA-256 OF EACH CASE'S INPUT BYTES, which is the
   real identity of a test case.  That key is NOT injective either — measured on
   the corpus, 1232 digests cover 5845 rows, because the same guest input appears
   under several manifest labels.  That is fine, and the script asserts the
   property that actually makes it fine: WITHIN a digest group, every case on a
   side must have the SAME guest output.  It must, since the emulator is
   deterministic and the input is byte-identical — so a violation means
   non-determinism, which is itself a finding rather than a join problem.
   (Verified on the corpus: 0 of 1232 groups disagree, on guest output or on
   expected output.)  Coverage is then asserted separately: every candidate case
   must have a base counterpart.

4. THE TWO LEGS ARE THE SAME BUILD.  `git checkout` CARRIES uncommitted changes
   across branches rather than refusing, so building the "base" leg after
   switching branches can silently pick up the candidate edit that was never
   committed.  Both legs then come from one source and the sweep reports a
   flawless zero.  Measured in practice: a 16-instruction deletion produced two
   byte-identical ELFs.  Asserted below (self-check 0) by comparing a digest of
   each guest's `.text` and `.data` plus the `.bss`, `.sszscratch`, and
   `.state_gas_diag` sizes.  The whole-file SHA is retained as provenance, but
   is not used as program identity because the ELF embeds its output basename.

   This one is the worst of the four, because ZERO DIFF IS THE PREDICTED RESULT
   for most refactors — the harness bug is indistinguishable from the hypothesis
   by looking at the output, so it cannot be caught downstream.

   RULE: build BOTH legs from COMMITTED refs, with a clean tree verified
   between them, per leg rather than once.

A denominator can be destroyed by a lossy join, not only by a truncated
enumeration.  So before trusting any cross-run comparison, establish that the
join is SOUND — either injective, or many-to-one with the property that makes
collapsing harmless asserted rather than assumed.  This script does that
mechanically, so it does not depend on whoever runs it remembering to.

RELATED, and NOT mechanised here because it happens before a run dir exists:
COMPARING EMITTED ELFs DIRECTLY.  The linker embeds the object filename, so
emitting to `-o base` and `-o cand` makes the two ELFs differ at the `base.o`
vs `cand.o` string even when the change is byte-neutral — a false defect.
Re-emitting under a third name to "control" for it reproduces the fault and
looks like nondeterministic emission.  Emit BOTH legs under the SAME output
name, then copy them apart.  An output path is an input to the linker.
General form of all of the above: A COMPARISON IS ONLY AS CLEAN AS THE THINGS
IT HOLDS EQUAL, and when layers disagree — `.s` and `.o` identical but `.elf`
differing — suspect the layer that differs from the others, not the change.

Exit status: 0 if every self-check passed AND no new false accepts appeared;
1 otherwise.  A failed self-check NEVER reports a verdict.
"""

from __future__ import annotations

import hashlib
import os
import struct
import sys
from collections import defaultdict
from dataclasses import dataclass


CAPTURED_OUTPUT_BYTES = 256


def scan_results(run_dir: str) -> tuple[dict[str, tuple[str, str]], list[str]]:
    """Return ``label -> (status, full_output_hex)`` and short captures.

    The result TSV intentionally stores only the fixture-sized prefix. For a
    successful case, the raw output file is the authoritative source for the
    A/B identity comparison, including diagnostic offsets 105..255.
    """
    out: dict[str, tuple[str, str]] = {}
    short_captures: list[str] = []
    suffix = ".result.tsv"
    try:
        entries = list(os.scandir(run_dir))
    except OSError as exc:
        sys.exit(f"error: cannot read run dir {run_dir}: {exc}")
    for entry in entries:
        if not entry.is_file() or not entry.name.endswith(suffix):
            continue
        label = entry.name[: -len(suffix)]
        try:
            with open(entry.path) as handle:
                fields = handle.read().strip().split("\t")
        except OSError:
            continue
        status = fields[0]
        output_hex = fields[1] if len(fields) > 1 else ""
        if status == "OK":
            output_path = os.path.join(run_dir, f"{label}.output")
            try:
                with open(output_path, "rb") as output_handle:
                    output = output_handle.read()
            except OSError:
                output = b""
            if len(output) < CAPTURED_OUTPUT_BYTES:
                short_captures.append(label)
            output_hex = output[:CAPTURED_OUTPUT_BYTES].hex()
        out[label] = (status, output_hex)
    return out, short_captures


def read_manifest(run_dir: str) -> dict[str, tuple[str, str, str]]:
    """label -> (input_path, expected_output_hex, fixture_relpath)."""
    path = os.path.join(run_dir, "manifest.tsv")
    rows: dict[str, tuple[str, str, str]] = {}
    try:
        handle = open(path)
    except OSError as exc:
        sys.exit(f"error: cannot read manifest {path}: {exc}")
    with handle:
        for line in handle:
            cols = line.rstrip("\n").split("\t")
            if len(cols) >= 7:
                rows[cols[0]] = (cols[1], cols[2], cols[6])
    return rows


@dataclass(frozen=True)
class ElfIdentity:
    """The part of a linked guest image that identifies its program.

    The whole ELF is not an identity: the linker embeds the output basename in
    the FILE symbol, so `.strtab` can change while the program does not.  The
    code/data sections and the guest's three NOBITS extents are the relevant
    image identity for this check.  The full-file SHA remains provenance in
    run-provenance.tsv.
    """

    section_digest: str
    bss_size: int
    sszscratch_size: int
    state_gas_diag_size: int
    path: str
    whole_file_sha: str


def provenance_field(run_dir: str, field: str) -> str | None:
    """Return one field from run-provenance.tsv, or None if it is unavailable.

    The provenance is written by codegen-eest-stateless-check.sh for every new
    run (GH #10617), including runs that supplied the guest with `--guest-elf`
    from outside the run dir.
    """
    path = os.path.join(run_dir, "run-provenance.tsv")
    try:
        with open(path) as handle:
            for line in handle:
                if line.startswith(field + "\t"):
                    return line.rstrip("\n").split("\t", 1)[1].strip() or None
    except OSError:
        return None
    return None


def provenance_guest_sha(run_dir: str) -> str | None:
    """`guest_elf_sha256` from the run's provenance, or None."""
    return provenance_field(run_dir, "guest_elf_sha256")


def guest_elf_path(run_dir: str) -> str | None:
    """Locate the ELF needed for section identity, or None.

    New run dirs record the resolved guest path.  Older run dirs may still have
    a local ELF copy without that field.  A legacy provenance file with only a
    whole-file SHA cannot establish section identity by itself, so it is
    handled as an explicit NOT RUN case rather than silently reusing the wrong
    identity.
    """
    recorded = provenance_field(run_dir, "guest_elf")
    if recorded and os.path.isfile(recorded):
        return recorded
    local = os.path.join(run_dir, "stateless_guest.elf")
    if os.path.isfile(local):
        return local
    return None


def read_elf_identity(path: str) -> ElfIdentity:
    """Read code bytes and guest NOBITS sizes from a 64-bit little-endian ELF.

    This intentionally parses the section table in Python instead of hashing
    the whole file or depending on a host-specific `readelf`/`objcopy` pair.
    Guest ELFs are RV64 little-endian ELF files; rejecting another format is a
    useful instrument failure, not evidence that the legs are distinct.
    """
    with open(path, "rb") as handle:
        image = handle.read()
    if len(image) < 64 or image[:4] != b"\x7fELF":
        raise ValueError("not an ELF file")
    if image[4] != 2 or image[5] != 1:
        raise ValueError("expected a 64-bit little-endian ELF")

    e_shoff = struct.unpack_from("<Q", image, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", image, 58)
    if e_shentsize < 64 or e_shnum == 0 or e_shstrndx >= e_shnum:
        raise ValueError("invalid ELF section table")
    table_end = e_shoff + e_shentsize * e_shnum
    if table_end > len(image):
        raise ValueError("ELF section table is outside the file")

    headers = []
    for index in range(e_shnum):
        offset = e_shoff + index * e_shentsize
        (name_offset, section_type, _flags, _address, file_offset, size,
         _link, _info, _alignment, _entry_size) = struct.unpack_from(
            "<IIQQQQIIQQ", image, offset
        )
        headers.append((name_offset, section_type, file_offset, size))

    _shstr_name_offset, shstr_type, shstr_file_offset, shstr_size = headers[e_shstrndx]
    if shstr_type == 8 or shstr_file_offset + shstr_size > len(image):
        raise ValueError("invalid ELF section-name string table")
    names = image[shstr_file_offset:shstr_file_offset + shstr_size]

    sections: dict[str, bytes | int] = {}
    for name_offset, section_type, file_offset, size in headers:
        if name_offset >= len(names):
            raise ValueError("invalid ELF section name offset")
        name_end = names.find(b"\0", name_offset)
        if name_end < 0:
            raise ValueError("unterminated ELF section name")
        name = names[name_offset:name_end].decode("ascii")
        if not name:
            continue
        if section_type == 8:  # SHT_NOBITS, notably .bss: no file payload.
            sections[name] = size
        else:
            if file_offset + size > len(image):
                raise ValueError(f"ELF section {name} is outside the file")
            sections[name] = image[file_offset:file_offset + size]

    try:
        text = sections[".text"]
        data = sections[".data"]
        bss_size = sections[".bss"]
        sszscratch_size = sections[".sszscratch"]
        state_gas_diag_size = sections[".state_gas_diag"]
        if not isinstance(text, bytes) or not isinstance(data, bytes):
            raise ValueError(".text/.data are not file-backed sections")
        if not all(isinstance(size, int) for size in
                   (bss_size, sszscratch_size, state_gas_diag_size)):
            raise ValueError("guest image size sections are not NOBITS sections")
    except KeyError as exc:
        raise ValueError(f"ELF is missing required section {exc.args[0]}") from exc

    digest = hashlib.sha256()
    for name, payload in ((b".text", text), (b".data", data)):
        digest.update(name + b"\0")
        digest.update(struct.pack("<Q", len(payload)))
        digest.update(payload)
    return ElfIdentity(digest.hexdigest(), bss_size, sszscratch_size,
                       state_gas_diag_size, path, hashlib.sha256(image).hexdigest())


def guest_elf_identity(run_dir: str) -> tuple[ElfIdentity | None, str | None]:
    """Return section identity and an explanatory failure reason, if any."""
    path = guest_elf_path(run_dir)
    if path is None:
        if provenance_guest_sha(run_dir) is not None:
            return None, ("legacy run-provenance.tsv records only the whole-file "
                          "SHA; no guest ELF path or local ELF is available")
        return None, "no guest ELF path or local stateless_guest.elf is available"
    try:
        identity = read_elf_identity(path)
        recorded_sha = provenance_guest_sha(run_dir)
        if recorded_sha is not None and identity.whole_file_sha != recorded_sha:
            return None, (f"guest ELF changed since the run: provenance SHA "
                          f"{recorded_sha[:16]}... but {path} is "
                          f"{identity.whole_file_sha[:16]}...")
        return identity, None
    except (OSError, ValueError, struct.error) as exc:
        return None, f"cannot read section identity from {path}: {exc}"


def succ(hexstr: str) -> str | None:
    """The validation bit: byte 32 of the output == hex chars [64:66]."""
    return hexstr[64:66].lower() if len(hexstr) >= 66 else None


def input_digest(path: str, cache: dict[str, str | None]) -> str | None:
    if path in cache:
        return cache[path]
    try:
        with open(path, "rb") as handle:
            digest: str | None = hashlib.sha256(handle.read()).hexdigest()
    except OSError:
        digest = None
    cache[path] = digest
    return digest


def classify(results, manifest):
    """-> (false_accepts, false_rejects, agreeing, unclassified) as label lists."""
    fa, fr, agree, unknown = [], [], [], []
    for label, (_status, out_hex) in results.items():
        entry = manifest.get(label)
        if entry is None:
            unknown.append(label)
            continue
        guest, expected = succ(out_hex), succ(entry[1])
        if guest is None or expected is None:
            unknown.append(label)
            continue
        guest_ok, expected_ok = guest == "01", expected == "01"
        if guest_ok and not expected_ok:
            fa.append(label)
        elif expected_ok and not guest_ok:
            fr.append(label)
        else:
            agree.append(label)
    return fa, fr, agree, unknown


def build_join(results, manifest, cache, side: str):
    """digest -> representative label, asserting WITHIN-GROUP output consistency.

    The digest is not injective (the same guest input recurs under several
    labels), which is harmless — but only because every case sharing an input
    must produce the same guest output.  That is asserted rather than assumed: a
    violation means non-determinism, which is a finding in its own right.
    """
    by_digest: dict[str, list[str]] = defaultdict(list)
    missing = 0
    for label in results:
        entry = manifest.get(label)
        if entry is None:
            missing += 1
            continue
        digest = input_digest(entry[0], cache)
        if digest is None:
            missing += 1
            continue
        by_digest[digest].append(label)

    grouped = {d: ls for d, ls in by_digest.items() if len(ls) > 1}
    inconsistent = {d: ls for d, ls in grouped.items()
                    if len({results[l] for l in ls}) > 1}
    if grouped:
        print(f"note: {side} side has {len(grouped)} shared-input group(s) covering "
              f"{sum(len(v) for v in grouped.values())} rows (join is many-to-one)")
    if inconsistent:
        print(f"!! NON-DETERMINISM on the {side} side: {len(inconsistent)} group(s) of "
              "byte-identical inputs produced DIFFERENT guest outputs")
        for digest, labels in list(inconsistent.items())[:3]:
            print(f"     {digest[:16]}… -> {len(labels)} labels disagree, "
                  f"e.g. {labels[0][:70]}")
    if missing:
        print(f"!! {missing} row(s) on the {side} side have no readable input file")
    return {d: ls[0] for d, ls in by_digest.items()}, (not inconsistent and not missing)


def main() -> int:
    if len(sys.argv) != 3:
        sys.exit(f"usage: {os.path.basename(sys.argv[0])} BASE_RUN_DIR CANDIDATE_RUN_DIR")
    base_dir, cand_dir = sys.argv[1], sys.argv[2]

    base_res, base_short = scan_results(base_dir)
    cand_res, cand_short = scan_results(cand_dir)
    base_man, cand_man = read_manifest(base_dir), read_manifest(cand_dir)

    print(f"base      {base_dir}: {len(base_res)} scored / {len(base_man)} manifest rows")
    print(f"candidate {cand_dir}: {len(cand_res)} scored / {len(cand_man)} manifest rows")

    ok = True

    for side, short_captures in (("BASE", base_short), ("CANDIDATE", cand_short)):
        if short_captures:
            print(f"!! {side} has {len(short_captures)} successful case(s) with less than "
                  f"{CAPTURED_OUTPUT_BYTES}-byte captured output -- cannot compare the "
                  "full output window")
            for label in short_captures[:3]:
                print(f"   SHORT {label[:70]}")
            ok = False

    # Self-check 0: the two legs must be DIFFERENT program images.  Comparing a
    # build to itself yields a flawless zero delta that means nothing, and the
    # ways it happens are silent: `git checkout` carries uncommitted changes
    # across branches, so building "base" after switching branches can pick up
    # the candidate edit that was never committed.  Zero diff is also the
    # PREDICTED result for many refactors, so the bug is indistinguishable from
    # the hypothesis by looking at the output -- it has to be caught here.
    for side, run_dir in (("BASE", base_dir), ("CANDIDATE", cand_dir)):
        full_sha = provenance_guest_sha(run_dir)
        if full_sha is not None:
            print(f"{side.lower()} whole-file SHA (provenance): {full_sha}")

    base_identity, base_identity_error = guest_elf_identity(base_dir)
    cand_identity, cand_identity_error = guest_elf_identity(cand_dir)
    if base_identity is None or cand_identity is None:
        unavailable = []
        if base_identity is None:
            unavailable.append(f"base ({base_identity_error})")
        if cand_identity is None:
            unavailable.append(f"candidate ({cand_identity_error})")
        print("note: self-check 0 NOT RUN -- section identity unavailable for "
              + "; ".join(unavailable))
    elif ((base_identity.section_digest, base_identity.bss_size,
           base_identity.sszscratch_size, base_identity.state_gas_diag_size)
          == (cand_identity.section_digest, cand_identity.bss_size,
              cand_identity.sszscratch_size, cand_identity.state_gas_diag_size)):
        print(f"!! BOTH LEGS HAVE THE SAME PROGRAM IMAGE: .text+.data sha256 "
              f"{base_identity.section_digest[:16]}..., "
              f".bss size 0x{base_identity.bss_size:x}, "
              f".sszscratch size 0x{base_identity.sszscratch_size:x}, "
              f".state_gas_diag size 0x{base_identity.state_gas_diag_size:x} "
              "-- this comparison is vacuous. Build each leg from a COMMITTED "
              "ref with a clean tree verified between them.")
        ok = False
    else:
        print("guest image identity: "
              f"base .text+.data {base_identity.section_digest[:16]}... "
              f"/.bss 0x{base_identity.bss_size:x} "
              f"/.sszscratch 0x{base_identity.sszscratch_size:x} "
              f"/.state_gas_diag 0x{base_identity.state_gas_diag_size:x}; "
              f"candidate .text+.data {cand_identity.section_digest[:16]}... "
              f"/.bss 0x{cand_identity.bss_size:x} "
              f"/.sszscratch 0x{cand_identity.sszscratch_size:x} "
              f"/.state_gas_diag 0x{cand_identity.state_gas_diag_size:x} "
              "(distinct program images)")

    # Self-check 2: denominators.  A candidate may be a deliberate --limit
    # sample; a BASE that did not score every row cannot anchor a delta.
    if len(base_res) != len(base_man):
        print(f"!! BASE INCOMPLETE: {len(base_res)} scored vs {len(base_man)} manifest rows "
              f"({len(base_man) - len(base_res)} missing) -- cannot anchor a delta")
        ok = False
    if len(cand_res) != len(cand_man):
        print(f"!! CANDIDATE INCOMPLETE: {len(cand_res)} scored vs {len(cand_man)} rows")
        ok = False
    sampled = len(cand_man) < len(base_man)
    if sampled:
        print(f"note: candidate is a SAMPLE ({len(cand_man)} of {len(base_man)}); "
              "reporting spot-confirmation over the sample, not a corpus delta")

    # Self-check 3: join-key uniqueness, on both sides, before any comparison.
    cache: dict[str, str | None] = {}
    base_join, base_ok = build_join(base_res, base_man, cache, "base")
    cand_join, cand_ok = build_join(cand_res, cand_man, cache, "candidate")
    ok = ok and base_ok and cand_ok

    common = set(cand_join) & set(base_join)
    coverage = len(common)
    unmatched = len(cand_join) - coverage
    print(f"joined on input-byte digest: {coverage} matched, {unmatched} unmatched")
    if unmatched:
        print(f"!! {unmatched} candidate case(s) have no base counterpart -- coverage incomplete")
        ok = False

    if not ok:
        print("\nSELF-CHECKS FAILED -- refusing to report a verdict. "
              "An FA/FR number over a broken denominator or a lossy join is not a result.")
        return 1
    print("self-checks: PASS (denominators complete, join sound "
          "— many-to-one with within-group output consistency asserted — coverage total)")

    bfa, bfr, bagree, bunk = classify(base_res, base_man)
    cfa, cfr, cagree, cunk = classify(cand_res, cand_man)
    print(f"\nbase      : FA={len(bfa)} FR={len(bfr)} agree={len(bagree)} unclassified={len(bunk)}")
    print(f"candidate : FA={len(cfa)} FR={len(cfr)} agree={len(cagree)} unclassified={len(cunk)}")

    status_diff, output_diff = [], []
    for digest in common:
        c, b = cand_res[cand_join[digest]], base_res[base_join[digest]]
        if c[0] != b[0]:
            status_diff.append(digest)
        if c[1] != b[1]:
            output_diff.append(digest)

    # FA/FR deltas are only meaningful corpus-wide; over a sample, report the
    # per-case comparison instead of a difference of two differently-sized sets.
    if not sampled:
        print(f"\nDELTA: FA {len(bfa)}->{len(cfa)} ({len(cfa) - len(bfa):+d})   "
              f"FR {len(bfr)}->{len(cfr)} ({len(cfr) - len(bfr):+d})")
        new_fa = set(cfa) - set(bfa)
        print(f"NEW FALSE ACCEPTS (must be empty): {len(new_fa)}")
        for label in sorted(new_fa)[:20]:
            print("   FA+", cand_man.get(label, ('', '', label))[2])
        if set(cfr) == set(bfr):
            print(f"FR LABEL-SET EQUALITY: PASS -- identical {len(cfr)}-label sets "
                  "(set equality, not a count match)")
        else:
            print(f"FR LABEL-SET EQUALITY: differs -- "
                  f"new={len(set(cfr) - set(bfr))} fixed={len(set(bfr) - set(cfr))}")
    else:
        new_fa = {label for label in cfa if label not in set(bfa)}

    print(f"\nstatus differences on joined cases : {len(status_diff)}")
    print(f"output-byte differences            : {len(output_diff)}")
    for digest in sorted(output_diff)[:20]:
        label = cand_join[digest]
        print("   OUT", cand_man.get(label, ('', '', label))[2])

    if not status_diff and not output_diff:
        scope = f"all {coverage} sampled cases" if sampled else f"all {coverage} cases"
        print(f"\nVERDICT: candidate is BYTE-IDENTICAL to base on {scope}.")
    return 1 if new_fa else 0


if __name__ == "__main__":
    sys.exit(main())
