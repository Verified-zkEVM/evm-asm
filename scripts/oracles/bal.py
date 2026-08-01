"""oracles.bal — BAL canonical ordering for the spec-correspondence oracle.

Reference: `_build_from_builder` in
`execution-specs/src/ethereum/forks/amsterdam/block_access_lists.py`.

This family's reference is **VENDORED** — it lives inside the execution-specs
submodule this repo pins by gitlink. Per docs/agents/spec-correspondence.md §6
that means it needs none of the external-package version machinery the RLP
family requires: no `uv.lock` lookup and no installed-version check, because the
gitlink is the pin and the corpus header stamps it.

It does still need the reference's own RUNTIME dependencies importable —
importing the fork package pulls in `ethereum_types` and `pycryptodome`. Vendored
pins the reference *code*, not its dependency closure. See the instance page's
Reproduce section for the exact env.

Method: docs/agents/spec-correspondence.md
Findings: docs/bal-spec-correspondence.md

Wire format (identical to EvmAsm/Tests/Correspondence/Bal.lean, which documents
it in full): one builder per line, accounts joined by `#`, an account's six
fields joined by `|`, slot groups by `/`, items by `;`, item fields by `,`.
Numbers decimal; addresses and code hex.

REPRESENTATION NOTE — why the corpus is deduplicated at generation. Python holds
`storage_changes: Dict[U256, ...]` and `storage_reads: Set[U256]`, so duplicate
slots and duplicate reads are impossible by construction. The Lean model uses
`List` for both, so it *can* represent states the reference cannot. Feeding a
duplicate-keyed input would report a "divergence" in a domain the real builder
can never enter — an artifact, not a finding. The corpus therefore stays inside
the reference's representable domain, and the gap is recorded on the instance
page instead.
"""

from __future__ import annotations

import pathlib
import sys

import spec_oracle
from spec_oracle import pins

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
SPECS_SRC = REPO_ROOT / "execution-specs" / "src"

if str(SPECS_SRC) not in sys.path:
    sys.path.insert(0, str(SPECS_SRC))

try:
    from ethereum.forks.amsterdam.block_access_lists import (  # noqa: E402
        AccountData,
        BalanceChange,
        BlockAccessListBuilder,
        CodeChange,
        NonceChange,
        StorageChange,
        _build_from_builder,
    )
    from ethereum.state import Address  # noqa: E402
    from ethereum_types.bytes import Bytes  # noqa: E402
    from ethereum_types.numeric import U64, U256  # noqa: E402
except ImportError as e:  # pragma: no cover - environment guard
    sys.stderr.write(
        f"error: cannot import the vendored BAL reference ({e}).\n"
        "The execution-specs submodule must be populated at the pinned rev:\n"
        "    git submodule update --init execution-specs\n"
        "Its runtime deps (ethereum_types) must also be importable.\n"
    )
    raise SystemExit(2)

BLOCK_ACCESS_INDEX = None
try:
    from ethereum.forks.amsterdam.fork_types import BlockAccessIndex

    BLOCK_ACCESS_INDEX = BlockAccessIndex
except ImportError:  # pragma: no cover
    BLOCK_ACCESS_INDEX = U64


# --------------------------------------------------------------------------
# Wire format
# --------------------------------------------------------------------------

def _parts(sep: str, s: str) -> list[str]:
    """`"".split(sep)` yields `[""]`; an absent field means no items."""
    return s.split(sep) if s else []


def parse_builder(line: str) -> BlockAccessListBuilder:
    builder = BlockAccessListBuilder()
    for acct in _parts("#", line):
        fields = acct.split("|")
        if len(fields) != 6:
            raise ValueError(f"account needs 6 fields, got {len(fields)}")
        addr_s, sc_s, reads_s, bals_s, nonces_s, codes_s = fields
        data = AccountData()
        for group in _parts("/", sc_s):
            slot_s, changes_s = group.split(":")
            changes = []
            for c in _parts(";", changes_s):
                i, v = c.split(",")
                changes.append(
                    StorageChange(BLOCK_ACCESS_INDEX(int(i)), U256(int(v))))
            data.storage_changes[U256(int(slot_s))] = changes
        for r in _parts(";", reads_s):
            data.storage_reads.add(U256(int(r)))
        for b in _parts(";", bals_s):
            i, v = b.split(",")
            data.balance_changes.append(
                BalanceChange(BLOCK_ACCESS_INDEX(int(i)), U256(int(v))))
        for n in _parts(";", nonces_s):
            i, v = n.split(",")
            data.nonce_changes.append(
                NonceChange(BLOCK_ACCESS_INDEX(int(i)), U64(int(v))))
        for c in _parts(";", codes_s):
            i, code = c.split(",")
            data.code_changes.append(
                CodeChange(BLOCK_ACCESS_INDEX(int(i)), Bytes(bytes.fromhex(code))))
        builder.accounts[Address(bytes.fromhex(addr_s))] = data
    return builder


def render(bal) -> str:
    out = []
    for a in bal:
        sc = "/".join(
            f"{int(g.slot)}:" + ";".join(
                f"{int(c.block_access_index)},{int(c.new_value)}" for c in g.changes)
            for g in a.storage_changes)
        reads = ";".join(str(int(r)) for r in a.storage_reads)
        bals = ";".join(
            f"{int(b.block_access_index)},{int(b.post_balance)}"
            for b in a.balance_changes)
        nonces = ";".join(
            f"{int(n.block_access_index)},{int(n.new_nonce)}"
            for n in a.nonce_changes)
        codes = ";".join(
            f"{int(c.block_access_index)},{bytes(c.new_code).hex()}"
            for c in a.code_changes)
        out.append("|".join([bytes(a.address).hex(), sc, reads, bals, nonces, codes]))
    return "#".join(out)


def accounts_already_ordered(builder: BlockAccessListBuilder, canonical) -> bool:
    """Were the accounts already in canonical address order?

    Scoped to the top-level account list on purpose. `storage_reads` is a `Set`,
    so its input order is destroyed before `_build_from_builder` runs — CPython
    iterates `{223, 75}` as `[75, 223]` — and a reads-based version of this axis
    would report "already canonical" for every input, measuring nothing. The
    accounts `Dict` preserves insertion order, so this question is well posed on
    both sides. Mirrors `runAccountsAlreadyOrdered` in the Lean subject.
    """
    input_addrs = [bytes(a).hex() for a in builder.accounts.keys()]
    canonical_addrs = [bytes(a.address).hex() for a in canonical]
    return input_addrs == canonical_addrs


# --------------------------------------------------------------------------
# Corpus
# --------------------------------------------------------------------------

def _acct(addr: str, sc="", reads="", bals="", nonces="", codes="") -> str:
    return "|".join([addr, sc, reads, bals, nonces, codes])


A1 = "aa" + "00" * 19
A2 = "bb" + "00" * 19
# The endian trap from EEST test_bal_lexicographic_address_ordering: byte-wise
# ascending must put 0x01..02 before 0x02..01, which an implementation that
# compared limbs in the wrong order would invert.
E1 = "01" + "00" * 18 + "02"
E2 = "02" + "00" * 18 + "01"


def boundary_cases() -> list[str]:
    """Cases the ordering verdicts actually turn on."""
    return [
        "",                                   # no accounts
        _acct(A1),                            # one account, all fields empty
        _acct(A2) + "#" + _acct(A1),          # accounts out of order
        _acct(A1) + "#" + _acct(A2),          # accounts already in order
        _acct(E2) + "#" + _acct(E1),          # endian trap, reversed
        _acct(E1) + "#" + _acct(E2),          # endian trap, in order

        # Slots sort NUMERICALLY, not by encoded bytes. RLP strips leading
        # zeros, so 255 encodes to 1 byte and 256 to 2 — encoded-byte order
        # would put 0x0100 before 0xff. These separate the two.
        _acct(A1, sc="256:1,7/255:1,7"),
        _acct(A1, sc="255:1,7/256:1,7"),
        _acct(A1, sc="1:1,1/16:1,1/2:1,1"),

        # Zero is the empty RLP string; make sure it orders as 0, not last.
        _acct(A1, sc="0:0,0/1:0,0"),
        _acct(A1, sc="1:0,0/0:0,0"),

        # Per-slot changes sort on block_access_index.
        _acct(A1, sc="5:3,30;1,10;2,20"),
        _acct(A1, sc="5:1,10;2,20;3,30"),

        # Read/write exclusion: a slot present in storage_changes must be
        # dropped from storage_reads.
        _acct(A1, sc="7:1,1", reads="7;9"),
        _acct(A1, reads="9;7"),
        _acct(A1, reads="256;255"),

        # Balance / nonce / code all sort on index.
        _acct(A1, bals="3,300;1,100;2,200"),
        _acct(A1, nonces="2,5;1,4"),
        _acct(A1, codes="2,beef;1,"),          # empty code is legal
        _acct(A1, codes="1,00;2,ff"),

        # Everything at once, thoroughly out of order.
        _acct(A2, sc="9:2,2;1,1/3:1,1", reads="8;4", bals="2,2;1,1",
              nonces="2,2;1,1", codes="2,aa;1,bb")
        + "#" + _acct(A1, sc="2:1,1/1:1,1", reads="5"),
    ]


def random_cases(count: int, seed: int) -> list[str]:
    """Randomized builders. The generator keeps slots and reads unique per
    account so every input stays inside the reference's representable domain
    (see the module docstring)."""
    gen = spec_oracle.lcg(seed)
    out: list[str] = []
    for _ in range(count):
        n_acct = next(gen) % 4
        accts = []
        for _ in range(n_acct):
            addr = f"{next(gen) % 256:02x}{next(gen) % 256:02x}" + "00" * 18
            slots = sorted({next(gen) % 300 for _ in range(next(gen) % 4)},
                           reverse=bool(next(gen) % 2))
            sc = "/".join(
                f"{s}:" + ";".join(
                    f"{next(gen) % 5},{next(gen) % 1000}"
                    for _ in range(1 + next(gen) % 2))
                for s in slots)
            read_pool = {next(gen) % 300 for _ in range(next(gen) % 4)}
            reads = ";".join(str(r) for r in sorted(read_pool, reverse=True))
            bals = ";".join(f"{next(gen) % 5},{next(gen) % 1000}"
                            for _ in range(next(gen) % 3))
            nonces = ";".join(f"{next(gen) % 5},{next(gen) % 100}"
                              for _ in range(next(gen) % 3))
            codes = ";".join(f"{next(gen) % 5},{next(gen) % 256:02x}"
                             for _ in range(next(gen) % 2))
            accts.append(_acct(addr, sc, reads, bals, nonces, codes))
        out.append("#".join(accts))
    return out


def corpus() -> list[str]:
    return boundary_cases() + random_cases(1500, seed=11)


# --------------------------------------------------------------------------
# Oracle
# --------------------------------------------------------------------------

def oracle(line: str) -> tuple[str, str, str]:
    try:
        builder = parse_builder(line)
    except Exception as e:
        return ("reject", f"{type(e).__name__}", "-")
    try:
        canonical_bal = _build_from_builder(builder)
        canonical = render(canonical_bal)
    except Exception as e:
        return ("reject", f"{type(e).__name__}", "-")
    ordered = "same" if accounts_already_ordered(builder, canonical_bal) else "differs"
    return ("accept", canonical, ordered)


FAMILY = spec_oracle.Family(
    name="bal",
    corpus=corpus,
    oracle=oracle,
    reference=pins.Vendored(
        "src/ethereum/forks/amsterdam/block_access_lists.py", REPO_ROOT),
    render_input=lambda s: s,
    aux_label="accounts-ordered",
)
