"""MPT decode family for the spec-correspondence oracle.

The boundary is deliberately decode-only.  An input carries a root RLP
preimage and, optionally, the RLP preimages of hash-addressed children.  The
oracle constructs ``node_db`` with the same ``build_node_db`` operation as the
stateless witness, then anchors ``decode_witness_to_mpt`` at the root hash.
This keeps authentication at the boundary while still allowing a withheld
child to become a ``HashedNode`` and be observed by a later lookup.

The family also covers the two pure decode helpers that feed that boundary:
``compact_to_nibbles`` and ``_decode_account_from_leaf``.  The wire format is
tagged so these three operations can share one committed corpus:

    compact|<compact bytes>
    node|<root RLP>|<child RLP>...
    missing|<root RLP>|<child RLP>...   # root deliberately omitted from DB
    account|<account-leaf RLP>

Node values are rendered as an S-expression.  The auxiliary axis checks that
an accepted RLP input round-trips through the reference RLP codec; compact
inputs are always ``same`` because they are not RLP values.
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
    from ethereum.forks.amsterdam.incremental_mpt import (
        HashedNode,
        MutableBranchNode,
        MutableExtensionNode,
        MutableLeafNode,
        _decode_witness_node,
        compact_to_nibbles,
        decode_witness_to_mpt,
    )
    from ethereum.forks.amsterdam.witness_state import (
        EMPTY_CODE_HASH,
        EMPTY_TRIE_ROOT,
        _decode_account_from_leaf,
        build_node_db,
    )
    from ethereum.crypto.hash import keccak256
    from ethereum_rlp import rlp
except ImportError as e:  # pragma: no cover - environment guard
    sys.stderr.write(
        f"error: cannot import the vendored MPT reference ({e}).\n"
        "The execution-specs submodule must be populated at the pinned rev:\n"
        "    git submodule update --init execution-specs\n"
        "Its runtime deps must also be importable.\n"
    )
    raise SystemExit(2)


def q(data: bytes) -> str:
    return f'"{bytes(data).hex()}"'


def render_node(node) -> str:
    if node is None:
        return "(node empty)"
    if isinstance(node, HashedNode):
        return f"(node hashed {q(node._hash)})"
    if isinstance(node, MutableLeafNode):
        return f"(node leaf {q(node.rest_of_key)} {q(node.value)})"
    if isinstance(node, MutableExtensionNode):
        return f"(node extension {q(node.key_segment)} {render_node(node.child)})"
    if isinstance(node, MutableBranchNode):
        children = " ".join(
            "none" if child is None else render_node(child)
            for child in node.children
        )
        return f"(node branch ({children}) {q(node.value)})"
    raise TypeError(f"unexpected MutableNode {type(node)!r}")


def render_account(result) -> str:
    account, storage_root = result
    return (
        f"(account {int(account.nonce)} {int(account.balance)} "
        f"{q(storage_root)} {q(account.code_hash)})"
    )


def split_hex_fields(line: str, tag: str) -> list[bytes]:
    fields = line.split("|")
    if not fields or fields[0] != tag or len(fields) < 2:
        raise ValueError("bad MPT wire tag or missing field")
    return [bytes.fromhex(field) for field in fields[1:]]


def oracle(line: str) -> tuple[str, str, str]:
    try:
        fields = line.split("|")
        tag = fields[0] if fields else ""

        if tag == "compact":
            if len(fields) != 2:
                raise ValueError("compact expects one field")
            nibbles, is_leaf = compact_to_nibbles(bytes.fromhex(fields[1]))
            return ("accept", f"(compact {q(nibbles)} {str(is_leaf).lower()})", "same")

        if tag in ("node", "missing"):
            nodes = split_hex_fields(line, tag)
            root = nodes[0]
            db_entries = nodes if tag == "node" else nodes[1:]
            node_db = build_node_db(tuple(db_entries))
            mpt = decode_witness_to_mpt(
                node_db, keccak256(root), secured=True, default=b""
            )
            detail = render_node(mpt.root_node)
            return ("accept", detail, "same" if rlp.encode(rlp.decode(root)) == root else "differs")

        if tag == "account":
            if len(fields) != 2:
                raise ValueError("account expects one field")
            leaf = bytes.fromhex(fields[1])
            detail = render_account(_decode_account_from_leaf(leaf))
            return ("accept", detail, "same" if rlp.encode(rlp.decode(leaf)) == leaf else "differs")

        raise ValueError("unknown MPT wire tag")
    except Exception as e:
        return ("reject", type(e).__name__, "-")


def _enc(item) -> str:
    return rlp.encode(item).hex()


def _leaf(path: bytes, value: bytes) -> bytes:
    return rlp.encode([path, value])


def _branch(children: list[object], value: bytes = b"") -> bytes:
    return rlp.encode(children + [value])


def _node(root: bytes, *children: bytes) -> str:
    return "node|" + "|".join(x.hex() for x in (root,) + children)


def _missing(root: bytes, *children: bytes) -> str:
    return "missing|" + "|".join(x.hex() for x in (root,) + children)


def _account(fields: list[bytes]) -> str:
    return "account|" + rlp.encode(fields).hex()


def boundary_cases() -> list[str]:
    leaf_ab = _leaf(bytes([0x20, 0xAB]), b"\x99")
    leaf_odd = _leaf(bytes([0x3B]), b"\x77")
    fat_leaf = _leaf(bytes([0x3B]), bytes([0x55] * 40))
    branch_inline = _branch(
        [leaf_odd if i in (0x0A, 0x0B) else b"" for i in range(16)]
    )
    branch_hashed = _branch(
        [keccak256(fat_leaf) if i in (0x0A, 0x0B) else b"" for i in range(16)]
    )
    ext_inline = rlp.encode([bytes([0x1A]), rlp.decode(branch_inline)])
    ext_hashed = rlp.encode([bytes([0x1A]), keccak256(branch_hashed)])
    account = _account([
        b"\x01", bytes.fromhex("0de0b6b3a7640000"),
        bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"),
        bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
    ])
    return [
        "compact|",
        "compact|00",
        "compact|01",
        "compact|1a",
        "compact|20",
        "compact|3b",
        "compact|ff00",
        "compact|20ab",
        _node(b"\x80"),
        _node(leaf_ab),
        _node(leaf_odd),
        _node(branch_inline),
        _node(branch_hashed, fat_leaf),
        _node(ext_inline),
        _node(ext_hashed, branch_hashed),
        _missing(branch_hashed),
        _missing(leaf_ab),
        _node(rlp.encode([bytes([0x1A]), rlp.decode(leaf_ab)])),
        _node(rlp.encode([bytes([0x00]), keccak256(branch_hashed)]), branch_hashed),
        _node(rlp.encode([bytes([0x1A]), keccak256(leaf_ab)]), leaf_ab),
        _node(_branch([b"\x01" if i == 0x0A else b"" for i in range(16)])),
        _node(_branch([b"\x01\x02" if i in (0x0A, 0x0B) else b"" for i in range(16)])),
        _node(rlp.encode([bytes([0x20]), rlp.encode([])])),
        _node(b"\x01"),
        _node(b"\xc1\x80"),
        _account([b"", b"", b"", b""]),
        _account([bytes([0] * 9), b"", bytes(32), bytes(32)]),
        _account([b"\x01", b"\x02", b"\x03"]),
        _account([b"\x01", b"\x02", b"\x03", b"\x04"]) + "00",
        "account|zz",
        "account|",
        "unknown|00",
        "node|zz",
    ]


def random_cases(count: int, seed: int) -> list[str]:
    gen = spec_oracle.lcg(seed)
    out: list[str] = []
    for _ in range(count):
        kind = next(gen) % 4
        if kind == 0:
            length = next(gen) % 6
            data = bytes(next(gen) % 256 for _ in range(length))
            out.append(f"compact|{data.hex()}")
        elif kind == 1:
            length = 1 + next(gen) % 12
            data = bytes(next(gen) % 256 for _ in range(length))
            out.append(f"node|{data.hex()}")
        elif kind == 2:
            fields = [bytes(next(gen) % 256 for _ in range(next(gen) % 8)) for _ in range(4)]
            out.append(_account(fields))
        else:
            n = 1 + next(gen) % 3
            nodes = [bytes(next(gen) % 256 for _ in range(1 + next(gen) % 20)) for _ in range(n)]
            out.append(_node(nodes[0], *nodes[1:]))
    return out


def corpus() -> list[str]:
    return boundary_cases() + random_cases(600, seed=37)


FAMILY = spec_oracle.Family(
    name="mpt",
    corpus=corpus,
    oracle=oracle,
    reference=pins.Vendored(
        "src/ethereum/forks/amsterdam/incremental_mpt.py", REPO_ROOT
    ),
    render_input=lambda s: s,
    aux_label="canonical-rlp",
)
