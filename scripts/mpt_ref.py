#!/usr/bin/env python3
"""Self-contained Merkle-Patricia-Trie reference for the stateless guest's
post-state-root recompute (mpt_set / mpt_root).

Used to generate (witness_nodes, root_hash, path_nibbles, new_value,
expected_new_root) test vectors and ziskemu `-i` probe inputs for the
`zisk_mpt_set` probe, and to cross-check the guest's RV64 implementation
byte-for-byte (the same discipline that validated mpt_walk and the node
encoders). RLP + keccak match Ethereum canonical encoding; verified here
against the guest's existing `single_leaf_trie_root` for the leaf case.

Scope of the FIRST milestone: VALUE-ONLY update of an EXISTING key (no
insert/delete, no structural change) — covers existing-account balance/
nonce updates and existing-slot updates, the bulk of state transitions.
The witness needs only the nodes ON THE PATH (root..leaf); a branch's
sibling slots are referenced by their unchanged refs inside the branch
RLP, so sibling bodies are not required.
"""
from __future__ import annotations
import struct, sys
from Crypto.Hash import keccak  # pycryptodome (available in execution-specs venv)


def k256(b: bytes) -> bytes:
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()


# ---- minimal RLP ----------------------------------------------------------
def rlp_len_prefix(length: int, base: int) -> bytes:
    if length < 56:
        return bytes([base + length])
    bl = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([base + 55 + len(bl)]) + bl


def rlp_bytes(b: bytes) -> bytes:
    if len(b) == 1 and b[0] < 0x80:
        return b
    return rlp_len_prefix(len(b), 0x80) + b


def rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(items)
    return rlp_len_prefix(len(payload), 0xC0) + payload


# ---- HP (hex-prefix) encoding ---------------------------------------------
def hp_encode(nibbles: list[int], is_leaf: bool) -> bytes:
    flag = (2 if is_leaf else 0) + (1 if len(nibbles) % 2 else 0)
    out = bytearray()
    if len(nibbles) % 2 == 1:
        out.append(flag * 16 + nibbles[0]); nibbles = nibbles[1:]
    else:
        out.append(flag * 16)
    for i in range(0, len(nibbles), 2):
        out.append(nibbles[i] * 16 + nibbles[i + 1])
    return bytes(out)


# ---- node encoders --------------------------------------------------------
def leaf_node(path_nibbles: list[int], value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path_nibbles, True)), rlp_bytes(value)])


def extension_node(path_nibbles: list[int], child_ref: bytes) -> bytes:
    # child_ref is an already-RLP-encoded item (0xa0||hash for hashed, or the
    # inline node RLP for <32B). It is concatenated verbatim into the list.
    return rlp_len_prefix(len(rlp_bytes(hp_encode(path_nibbles, False))) + len(child_ref), 0xC0) + \
           rlp_bytes(hp_encode(path_nibbles, False)) + child_ref


def branch_node(slots: list[bytes], value: bytes = b"") -> bytes:
    # slots: 16 already-RLP-encoded child refs (each b"\x80" if empty, else
    # the inline node RLP or 0xa0||hash); value is the 17th item.
    payload = b"".join(slots) + rlp_bytes(value)
    return rlp_len_prefix(len(payload), 0xC0) + payload


def node_ref(node_rlp: bytes) -> bytes:
    """The reference to a node as it appears inside its parent: the inline
    node RLP if <32 bytes, else 0xa0 || keccak256(node_rlp)."""
    if len(node_rlp) < 32:
        return node_rlp
    return b"\xa0" + k256(node_rlp)


def trie_root(root_node_rlp: bytes) -> bytes:
    """Root hash of a trie whose root node is root_node_rlp."""
    if len(root_node_rlp) < 32:
        return k256(root_node_rlp)  # tiny tries still hash the root
    return k256(root_node_rlp)


# ---- ziskemu probe input (mirrors mpt_walk's layout, + new_value) ---------
#   INPUT+8  : witness_len           INPUT+16 : path_len (nibbles)
#   INPUT+24 : new_value_len         INPUT+32 : root_hash (32B)
#   INPUT+64 : path_nibbles (1B each), then new_value, then witness section
def build_probe_input(root_hash, path_nibbles, new_value, witness_section) -> bytes:
    body = bytearray()
    body += struct.pack("<Q", len(witness_section))   # +8
    body += struct.pack("<Q", len(path_nibbles))      # +16
    body += struct.pack("<Q", len(new_value))         # +24
    body += root_hash                                 # +32 .. +64
    body += bytes(path_nibbles)                        # +64 ..
    body += new_value
    # 8-align before the witness section
    while len(body) % 8 != 0:
        body += b"\x00"
    body += witness_section
    # ziskemu maps the probe file directly to INPUT+8 (the probe reads its
    # first field at INPUT+8 == file[0:8]); no outer length prefix.
    body += b"\x00" * ((-len(body)) % 8)
    return bytes(body)


def ssz_section(elements: list[bytes]) -> bytes:
    """SSZ List[ByteList] wire form: u32 offset table then concatenated bodies
    (matches witness.state, what witness_lookup_by_hash scans)."""
    out = bytearray(); off = 4 * len(elements)
    for e in elements:
        out += struct.pack("<I", off); off += len(e)
    for e in elements:
        out += e
    return bytes(out)


# ---- vector shapes (value-only update of an existing key) -----------------
# On-path leaves in the branch/ext shapes use a >=32-byte value so their RLP
# hashes (node_ref => 0xa0||keccak): then EVERY on-path node is a distinct
# witness element with a clean section-relative byte offset, which the
# record-walk reports and the reference predicts without modelling
# inline-child positions. (The leaf shape's single leaf is found via
# root_hash regardless of size, so it stays short.)
A_OLD = b"a" * 32                  # forces la_old to hash
A_NEW = b"a-new-value-xyz"         # new value (record-walk ignores it)


def vec_leaf():
    """Trie = single leaf (root). key path = full 4 nibbles. depth 0."""
    path = [0x1, 0x2, 0x3, 0x4]
    old, new = b"old-value", b"new-value-1234"
    root_node = leaf_node(path, old)
    new_root_node = leaf_node(path, new)
    # levels: the non-terminal (branch/extension) nodes on the path, in
    # root->leaf order. (kind, nibble, nibbles_consumed). Empty for a leaf.
    return dict(name="leaf", witness=[root_node], root=trie_root(root_node),
                path=path, new_value=new, expected=trie_root(new_root_node),
                levels=[])


def vec_branch():
    """Trie = branch(root) with two leaf children at nibble 1 and 2. Update
    the child at nibble 1 (path 1,a,b). depth 1."""
    la_path, lb_path = [0xa, 0xb], [0xc, 0xd]
    b_val = b"b-val"
    la_old = leaf_node(la_path, A_OLD); lb = leaf_node(lb_path, b_val)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la_old); slots[2] = node_ref(lb)
    root_node = branch_node(slots)
    # update: child at nibble 1 -> new value
    la_new = leaf_node(la_path, A_NEW)
    slots2 = list(slots); slots2[1] = node_ref(la_new)
    new_root_node = branch_node(slots2)
    witness = [root_node, la_old]  # path nodes (lb not needed for value-only)
    return dict(name="branch", witness=witness, root=trie_root(root_node),
                path=[0x1] + la_path, new_value=A_NEW,
                expected=trie_root(new_root_node),
                levels=[("branch", 0x1, 1)])


def vec_ext_branch():
    """Trie = extension(root, prefix=[5,6]) -> branch -> two leaves. Update
    child at nibble 1 (path 5,6,1,a,b). depth 2."""
    ext_prefix = [0x5, 0x6]
    la_path, lb_path = [0xa, 0xb], [0xc, 0xd]
    b_val = b"b-val"
    la_old = leaf_node(la_path, A_OLD); lb = leaf_node(lb_path, b_val)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la_old); slots[2] = node_ref(lb)
    branch = branch_node(slots)
    root_node = extension_node(ext_prefix, node_ref(branch))
    # update
    la_new = leaf_node(la_path, A_NEW)
    slots2 = list(slots); slots2[1] = node_ref(la_new)
    branch2 = branch_node(slots2)
    new_root_node = extension_node(ext_prefix, node_ref(branch2))
    witness = [root_node, branch, la_old]
    return dict(name="ext_branch", witness=witness, root=trie_root(root_node),
                path=ext_prefix + [0x1] + la_path, new_value=A_NEW,
                expected=trie_root(new_root_node),
                levels=[("extension", 0, len(ext_prefix)),
                        ("branch", 0x1, 1)])


VECTORS = [vec_leaf, vec_branch, vec_ext_branch]


# ---- accumulating (2 sequential updates) vector (mpt_set_acc .4.3.1) -------
# Two value-only updates applied in sequence to a branch trie: update key A
# (nibble 1), then key B (nibble 2) starting from the NEW root. This forces
# the appendable node DB: update 2's walk starts at update 1's new root
# (only in the DB, not the witness) and descends into the unchanged sibling
# leaf (resolved from the witness). Both old leaves are >=32 bytes so they
# are hash-referenced (distinct witness elements), and the new root branch is
# itself >=32 so it is hash-keyed in the DB.
def build_acc_probe_input(root_hash, p1, v1, p2, v2, witness_section) -> bytes:
    """ziskemu `-i` body for zisk_mpt_set_acc (file maps to INPUT+8):
      +8 witness_len | +16 path1_len | +24 value1_len | +32 path2_len
      +40 value2_len | +48 root_hash(32B) | +80 path1 | value1 | path2
      | value2 | witness  -- each variable segment padded to 8 bytes."""
    body = bytearray()
    body += struct.pack("<Q", len(witness_section))   # +8
    body += struct.pack("<Q", len(p1))                # +16
    body += struct.pack("<Q", len(v1))                # +24
    body += struct.pack("<Q", len(p2))                # +32
    body += struct.pack("<Q", len(v2))                # +40
    body += root_hash                                 # +48 .. +80
    for seg in (bytes(p1), v1, bytes(p2), v2, witness_section):
        body += seg
        while len(body) % 8 != 0:
            body += b"\x00"
    return bytes(body)


def vec_acc():
    la_path, lb_path = [0xa, 0xb], [0xc, 0xd]
    a_old, b_old = b"a" * 32, b"b" * 32          # >=32 => hashed children
    v1, v2 = b"v1-new", b"v2-new-value-padded-to-thirty2!"
    la_old = leaf_node(la_path, a_old); lb_old = leaf_node(lb_path, b_old)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la_old); slots[2] = node_ref(lb_old)
    root_node = branch_node(slots)
    witness = [root_node, la_old, lb_old]
    # expected final trie after both updates
    la_new = leaf_node(la_path, v1); lb_new = leaf_node(lb_path, v2)
    fslots = list(slots)
    fslots[1] = node_ref(la_new); fslots[2] = node_ref(lb_new)
    final_root_node = branch_node(fslots)
    return dict(name="acc", witness=witness, root=trie_root(root_node),
                path1=[0x1] + la_path, value1=v1,
                path2=[0x2] + lb_path, value2=v2,
                expected=trie_root(final_root_node))


# ---- multi-change driver vector (mpt_state_root .4.3.2) -------------------
def build_state_root_input(root_hash, changes, witness_section) -> bytes:
    """ziskemu `-i` body for zisk_mpt_state_root (file maps to INPUT+8):
      +8 witness_len | +16 n_changes | +24 root_hash(32B)
      +56 lengths table: N x (path_len:u64, value_len:u64)
      then blobs path0,value0,... (each 8-aligned) | witness (8-aligned).
    changes = list of (path_nibbles, value_bytes)."""
    body = bytearray()
    body += struct.pack("<Q", len(witness_section))   # +8
    body += struct.pack("<Q", len(changes))           # +16
    body += root_hash                                 # +24 .. +56
    for (p, v) in changes:                            # lengths table
        body += struct.pack("<Q", len(p)) + struct.pack("<Q", len(v))
    for (p, v) in changes:                            # blobs, 8-aligned each
        body += bytes(p)
        while len(body) % 8 != 0:
            body += b"\x00"
        body += v
        while len(body) % 8 != 0:
            body += b"\x00"
    body += witness_section
    while len(body) % 8 != 0:
        body += b"\x00"
    return bytes(body)


def vec_state_root():
    """Branch trie with three hashed leaf children (nibbles 1,2,3); update
    all three in sequence -> final root. Exercises the multi-change driver
    threading mpt_set_acc through the appendable node DB."""
    paths = {1: [0xa, 0xb], 2: [0xc, 0xd], 3: [0xe, 0xf]}
    olds = {1: b"a" * 32, 2: b"b" * 32, 3: b"c" * 32}   # hashed children
    news = {1: b"x1-new", 2: b"y2-new-value-padded-to-thirty2!!", 3: b"z3"}
    old_leaves = {k: leaf_node(paths[k], olds[k]) for k in (1, 2, 3)}
    slots = [b"\x80"] * 16
    for k in (1, 2, 3):
        slots[k] = node_ref(old_leaves[k])
    root_node = branch_node(slots)
    witness = [root_node] + [old_leaves[k] for k in (1, 2, 3)]
    fslots = list(slots)
    for k in (1, 2, 3):
        fslots[k] = node_ref(leaf_node(paths[k], news[k]))
    final_root_node = branch_node(fslots)
    changes = [([k] + paths[k], news[k]) for k in (1, 2, 3)]
    return dict(name="state_root", witness=witness, root=trie_root(root_node),
                changes=changes, expected=trie_root(final_root_node))


# ---- record-walk expectation (mpt_set .4.2.1) -----------------------------
def element_offsets(witness: list[bytes]) -> list[int]:
    """Byte offset of each element BODY within an ssz_section: the u32 offset
    table (4 bytes/element) followed by the concatenated bodies."""
    base = 4 * len(witness); offs = []; cur = base
    for e in witness:
        offs.append(cur); cur += len(e)
    return offs


def record_walk_expected(v: dict) -> list[tuple[str, int, int]]:
    """Expected probe OUTPUT fields for `zisk_mpt_set_record_walk` as
    (name, byte_offset_in_output, u64_value). Mirrors the asm descent: every
    on-path node is witness element i (path order); records 0..depth-1 are
    the branch/extension nodes, the terminal (leaf) is element `depth`.

    OUTPUT layout: status@0, meta(depth,consumed,leaf_offset,leaf_len)@8,
    records (offset,len,kind,nibble) 32 B each @128.
    """
    witness, levels = v["witness"], v["levels"]
    offs = element_offsets(witness)
    depth = len(levels)
    assert depth == len(witness) - 1, f"{v['name']}: depth/witness mismatch"
    consumed = sum(consumed_n for (_k, _nib, consumed_n) in levels)
    out = [
        ("status", 0, 0),
        ("depth", 8, depth),
        ("consumed", 16, consumed),
        ("leaf_offset", 24, offs[depth]),
        ("leaf_len", 32, len(witness[depth])),
    ]
    for i, (kind, nibble, _c) in enumerate(levels):
        base = 128 + 32 * i
        out += [
            (f"rec{i}_offset", base + 0, offs[i]),
            (f"rec{i}_len", base + 8, len(witness[i])),
            (f"rec{i}_kind", base + 16, 0 if kind == "branch" else 1),
            (f"rec{i}_nibble", base + 24, nibble),
        ]
    return out

# ---- account RLP balance update (mpt account_add_balance .2.1) ------------
def minimal_be(x: int) -> bytes:
    return b"" if x == 0 else x.to_bytes((x.bit_length() + 7) // 8, "big")


def rlp_int(x: int) -> bytes:
    return rlp_bytes(minimal_be(x))


def account_encode(nonce: int, balance: int, sroot: bytes, chash: bytes) -> bytes:
    """Ethereum account RLP: rlp([nonce, balance, storageRoot, codeHash])."""
    return rlp_list([rlp_int(nonce), rlp_int(balance),
                     rlp_bytes(sroot), rlp_bytes(chash)])


def build_aab_input(account: bytes, delta: int) -> bytes:
    """ziskemu `-i` body for zisk_account_add_balance (file -> INPUT+8):
      +8 account_len | +16 delta(32B BE) | +48 account RLP."""
    body = struct.pack("<Q", len(account)) + delta.to_bytes(32, "big") + account
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


def vec_account_add_balance():
    sroot, chash = b"\x11" * 32, b"\x22" * 32
    # (name, nonce, balance, delta) — covers byte growth, 0-start, 8-byte
    # carry boundary, and a +0 no-op.
    cases = [
        ("aab1", 1, 0xff, 1),            # 255 + 1 = 256 (grows 1 -> 2 bytes)
        ("aab2", 0, 0, 10 ** 18),        # 0 + 1e18 (empty -> multi-byte)
        ("aab3", 5, 2 ** 64 - 1, 1),     # carry across the 8-byte boundary
        ("aab4", 7, 0, 0),               # +0 no-op (balance stays empty)
    ]
    out = []
    for name, nonce, bal, delta in cases:
        out.append(dict(name=name,
                        account=account_encode(nonce, bal, sroot, chash),
                        delta=delta,
                        expected=account_encode(nonce, bal + delta, sroot, chash)))
    return out


def bal_account_change_rlp(address: bytes,
                           storage_changes: list[bytes] | None = None,
                           storage_reads: list[bytes] | None = None,
                           balance_changes: list[tuple[int, int]] | None = None,
                           nonce_changes: list[tuple[int, int]] | None = None,
                           code_changes: list[tuple[int, bytes]] | None = None) -> bytes:
    def change_pair(index: int, value_rlp: bytes) -> bytes:
        return rlp_list([rlp_int(index), value_rlp])

    storage_changes = storage_changes or []
    storage_reads = storage_reads or []
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    code_changes = code_changes or []
    sc = [rlp_list([rlp_bytes(slot), rlp_list([])]) for slot in storage_changes]
    sr = [rlp_bytes(slot) for slot in storage_reads]
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    cc = [change_pair(i, rlp_bytes(code)) for i, code in code_changes]
    return rlp_list([rlp_bytes(address), rlp_list(sc), rlp_list(sr),
                     rlp_list(bc), rlp_list(nc), rlp_list(cc)])


def build_bacp_input(account_change: bytes) -> bytes:
    body = struct.pack("<Q", len(account_change)) + account_change
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


def vec_bal_account_path():
    cases = [
        ("bacp_empty", bytes.fromhex("00112233445566778899aabbccddeeff00112233"), {}),
        ("bacp_changes", bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b"),
         dict(storage_reads=[(0x200b).to_bytes(2, "big")],
              balance_changes=[(1, 5), (2, 10 ** 10)],
              nonce_changes=[(1, 1)])),
        ("bacp_precompile", bytes.fromhex("0000000000000000000000000000000000000001"),
         dict(balance_changes=[(1, 10 ** 10)])),
    ]
    return [dict(name=name,
                 account_change=bal_account_change_rlp(addr, **kwargs),
                 path=bytes_to_nibbles_py(k256(addr)))
            for name, addr, kwargs in cases]


# ---- withdrawal -> (path, wei delta) preprocessing (.2.2.1) ---------------
def withdrawal_rlp(index: int, vindex: int, address: bytes, amount: int) -> bytes:
    """Shanghai+ withdrawal RLP: rlp([index, validator_index, address, amount])."""
    def ri(x: int) -> bytes:  # minimal-int RLP (local, avoids cross-branch clash)
        return rlp_bytes(b"" if x == 0 else x.to_bytes((x.bit_length() + 7) // 8, "big"))
    return rlp_list([ri(index), ri(vindex), rlp_bytes(address), ri(amount)])


def bytes_to_nibbles_py(b: bytes) -> bytes:
    out = bytearray()
    for byte in b:
        out.append(byte >> 4)
        out.append(byte & 0xF)
    return bytes(out)


def vec_withdrawal_to_path_delta():
    cases = [
        ("wtpd1", 0, 5, bytes.fromhex("00112233445566778899aabbccddeeff00112233"), 1),
        ("wtpd2", 7, 99, b"\xab" * 20, 32 * 10 ** 9),   # ~32 ETH in Gwei
        ("wtpd3", 1, 1, bytes(range(20)), 2 ** 40),
    ]
    out = []
    for name, idx, vidx, addr, amt in cases:
        out.append(dict(name=name,
                        wd=withdrawal_rlp(idx, vidx, addr, amt),
                        path=bytes_to_nibbles_py(k256(addr)),     # 64 nibbles
                        delta=(amt * 10 ** 9).to_bytes(32, "big")))
    return out


def build_asuf_input(account: bytes, field_index: int, value: int) -> bytes:
    """ziskemu `-i` body for zisk_account_set_uint_field (file -> INPUT+8):
      +8 account_len | +16 field_index | +24 value_len | +32 value bytes | +64 account RLP."""
    vb = minimal_be(value)
    body = (struct.pack("<Q", len(account)) + struct.pack("<Q", field_index) +
            struct.pack("<Q", len(vb)) + vb + b"\x00" * (32 - len(vb)) + account)
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


def vec_account_set_uint_field():
    sroot, chash = b"\x11" * 32, b"\x22" * 32
    account = account_encode(1, 0xff, sroot, chash)
    cases = [
        ("asuf_nonce", account, 0, 2, account_encode(2, 0xff, sroot, chash)),
        ("asuf_balance", account, 1, 0x0100, account_encode(1, 0x0100, sroot, chash)),
        ("asuf_zero_balance", account, 1, 0, account_encode(1, 0, sroot, chash)),
    ]
    return [dict(name=name, account=acct, field_index=field, value=value, expected=expected)
            for name, acct, field, value, expected in cases]


def build_selfdestruct_balance_input(origin: bytes, beneficiary: bytes,
                                     same_address: int, created_in_tx: int) -> bytes:
    """ziskemu `-i` body for zisk_selfdestruct_balance_transfer:
      +8 origin_len | +16 beneficiary_len | +24 same flag | +32 created flag
      +40 origin account RLP fixed 512-byte slot | +552 beneficiary account RLP."""
    if len(origin) > 512 or len(beneficiary) > 512:
        raise ValueError("account fixture exceeds fixed probe slot")
    body = (struct.pack("<Q", len(origin)) + struct.pack("<Q", len(beneficiary)) +
            struct.pack("<Q", same_address) + struct.pack("<Q", created_in_tx) +
            origin + b"\x00" * (512 - len(origin)) + beneficiary)
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


def vec_selfdestruct_balance_transfer():
    sroot, chash = b"\x11" * 32, b"\x22" * 32
    origin = account_encode(3, 123456789, sroot, chash)
    beneficiary = account_encode(4, 9, b"\x33" * 32, b"\x44" * 32)
    same = account_encode(5, 777, sroot, chash)
    cases = [
        ("sdbt_diff", origin, beneficiary, 0, 0,
         account_encode(3, 0, sroot, chash),
         account_encode(4, 123456798, b"\x33" * 32, b"\x44" * 32)),
        ("sdbt_same_keep", same, same, 1, 0, same, same),
        ("sdbt_same_burn", same, same, 1, 1,
         account_encode(5, 0, sroot, chash),
         account_encode(5, 0, sroot, chash)),
    ]
    return [dict(name=name, origin=src, beneficiary=dst,
                 same_address=same_flag, created_in_tx=created_flag,
                 expected_origin=expected_src, expected_beneficiary=expected_dst)
            for name, src, dst, same_flag, created_flag, expected_src, expected_dst in cases]

# ---- withdrawal -> (path, wei delta) preprocessing (.2.2.1) ---------------
def withdrawal_rlp(index: int, vindex: int, address: bytes, amount: int) -> bytes:
    """Shanghai+ withdrawal RLP: rlp([index, validator_index, address, amount])."""
    def ri(x: int) -> bytes:  # minimal-int RLP (local, avoids cross-branch clash)
        return rlp_bytes(b"" if x == 0 else x.to_bytes((x.bit_length() + 7) // 8, "big"))
    return rlp_list([ri(index), ri(vindex), rlp_bytes(address), ri(amount)])


def bytes_to_nibbles_py(b: bytes) -> bytes:
    out = bytearray()
    for byte in b:
        out.append(byte >> 4)
        out.append(byte & 0xF)
    return bytes(out)


def vec_withdrawal_to_path_delta():
    cases = [
        ("wtpd1", 0, 5, bytes.fromhex("00112233445566778899aabbccddeeff00112233"), 1),
        ("wtpd2", 7, 99, b"\xab" * 20, 32 * 10 ** 9),   # ~32 ETH in Gwei
        ("wtpd3", 1, 1, bytes(range(20)), 2 ** 40),
    ]
    out = []
    for name, idx, vidx, addr, amt in cases:
        out.append(dict(name=name,
                        wd=withdrawal_rlp(idx, vidx, addr, amt),
                        path=bytes_to_nibbles_py(k256(addr)),     # 64 nibbles
                        delta=(amt * 10 ** 9).to_bytes(32, "big")))
    return out


# ---- withdrawal-driven post-state-root recompute (.2.2) -------------------
def build_wsr_input(root_hash, wds, witness_section) -> bytes:
    """ziskemu `-i` body for zisk_withdrawals_state_root (file -> INPUT+8):
      +8 witness_len | +16 n_wds | +24 root_hash(32B)
      +56 wd length table N x u64 | blobs (8-aligned each) | witness."""
    body = bytearray(struct.pack("<Q", len(witness_section)) +
                     struct.pack("<Q", len(wds)) + root_hash)
    for wd in wds:
        body += struct.pack("<Q", len(wd))
    for wd in wds:
        body += wd
        while len(body) % 8 != 0:
            body += b"\x00"
    body += witness_section
    while len(body) % 8 != 0:
        body += b"\x00"
    return bytes(body)


def vec_withdrawals_state_root():
    """State trie with two accounts whose key paths (keccak(address)) diverge
    at nibble 0 (root is a branch with two hashed leaf children); credit both
    via withdrawals; expected post-state root after the value-only updates."""
    sroot, chash = b"\x11" * 32, b"\x22" * 32
    # pick two addresses whose keccak first nibble differs (root branch only).
    cands = [(bytes([i]) * 20, k256(bytes([i]) * 20)[0] >> 4) for i in range(1, 256)]
    addr1, n1f = cands[0]
    addr2, _ = next(c for c in cands if c[1] != n1f)
    nib1 = bytes_to_nibbles_py(k256(addr1))
    nib2 = bytes_to_nibbles_py(k256(addr2))
    nonce1, bal1, amt1 = 1, 10 ** 18, 32 * 10 ** 9
    nonce2, bal2, amt2 = 2, 5 * 10 ** 17, 16 * 10 ** 9

    def trie(b1, b2):
        l1 = leaf_node(list(nib1[1:]), account_encode(nonce1, b1, sroot, chash))
        l2 = leaf_node(list(nib2[1:]), account_encode(nonce2, b2, sroot, chash))
        slots = [b"\x80"] * 16
        slots[nib1[0]] = node_ref(l1)
        slots[nib2[0]] = node_ref(l2)
        return branch_node(slots), l1, l2

    root_node, leaf1, leaf2 = trie(bal1, bal2)
    new_root_node, _, _ = trie(bal1 + amt1 * 10 ** 9, bal2 + amt2 * 10 ** 9)
    return dict(witness=[root_node, leaf1, leaf2], root=trie_root(root_node),
                wds=[withdrawal_rlp(0, 100, addr1, amt1),
                     withdrawal_rlp(1, 101, addr2, amt2)],
                expected=trie_root(new_root_node))


# ---- insert-walk divergence vectors (mpt_insert_walk .2.4.2.6.1) ----------
# Each vector is a trie + an ABSENT path; the walk must classify WHERE the path
# diverges and record the terminal node + ancestor stack for a later insert.
EMPTY_TRIE_ROOT = bytes.fromhex(
    "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")


def vec_iw_branch_empty():
    """Root = branch with an inline leaf at nibble 1. Insert path starts at
    nibble 3 (empty slot) -> case 0 BRANCH_EMPTY_SLOT, terminal = root branch,
    depth 0 (the branch is un-pushed), consumed 0."""
    la = leaf_node([0xa, 0xb], b"v1")
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la)
    root = branch_node(slots)
    return dict(name="iw_branch_empty", witness=[root], root=trie_root(root),
                path=[0x3, 0x7, 0x8],
                case=0, depth=0, consumed=0, match_len=0,
                terminal_index=0, levels=[])


def vec_iw_leaf_split():
    """Root = leaf key [1,2,3,4]. Insert path [1,2,9,9] diverges at the leaf
    with shared prefix [1,2] -> case 1 LEAF_SPLIT, match_len 2."""
    root = leaf_node([0x1, 0x2, 0x3, 0x4], b"leaf-value")
    return dict(name="iw_leaf_split", witness=[root], root=trie_root(root),
                path=[0x1, 0x2, 0x9, 0x9],
                case=1, depth=0, consumed=0, match_len=2,
                terminal_index=0, levels=[])


def vec_iw_ext_split():
    """Root = extension prefix [5,6] -> branch. Insert path [5,9,0,0] diverges
    inside the extension at position 1 -> case 2 EXTENSION_SPLIT, match_len 1."""
    la = leaf_node([0xa, 0xb], b"x" * 32)
    lb = leaf_node([0xc, 0xd], b"y" * 32)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la)
    slots[2] = node_ref(lb)
    branch = branch_node(slots)
    root = extension_node([0x5, 0x6], node_ref(branch))
    return dict(name="iw_ext_split", witness=[root], root=trie_root(root),
                path=[0x5, 0x9, 0x0, 0x0],
                case=2, depth=0, consumed=0, match_len=1,
                terminal_index=0, levels=[])


def vec_iw_empty_trie():
    """Root = EMPTY_TRIE_ROOT -> case 3 EMPTY_TRIE (single new leaf)."""
    return dict(name="iw_empty_trie", witness=[], root=EMPTY_TRIE_ROOT,
                path=[0x1, 0x2],
                case=3, depth=0, consumed=0, match_len=0,
                terminal_index=None, levels=[])


def vec_iw_ext_then_branch_empty():
    """Root = extension [5,6] -> branch B (>=32, hash-referenced) with an inline
    leaf at nibble 1. Insert path [5,6,3,c]: the extension matches fully (pushed
    as an ancestor), then branch B's slot 3 is empty -> case 0 BRANCH_EMPTY_SLOT,
    depth 1, consumed 2, terminal = branch B."""
    la = leaf_node([0xc], b"z" * 40)            # big -> branch B > 32 bytes
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la)
    branch = branch_node(slots)
    assert len(branch) >= 32, "branch must be hash-referenced for this vector"
    root = extension_node([0x5, 0x6], node_ref(branch))
    return dict(name="iw_ext_then_branch_empty",
                witness=[root, branch], root=trie_root(root),
                path=[0x5, 0x6, 0x3, 0xc],
                case=0, depth=1, consumed=2, match_len=0,
                terminal_index=1, levels=[("extension", 0, 2)])


IW_VECTORS = [vec_iw_branch_empty, vec_iw_leaf_split, vec_iw_ext_split,
              vec_iw_empty_trie, vec_iw_ext_then_branch_empty]


def insert_walk_expected(v: dict) -> list[tuple[str, int, int]]:
    """Expected probe OUTPUT for zisk_mpt_insert_walk as (name, offset, value).
    OUTPUT: status@0, meta(depth@8, consumed@16, case@24, terminal_offset@32,
    terminal_len@40, match_len@48), ancestor records 32 B each @128."""
    witness, levels = v["witness"], v["levels"]
    offs = element_offsets(witness)
    if v["terminal_index"] is None:
        term_off, term_len = 0, 0
    else:
        ti = v["terminal_index"]
        term_off, term_len = offs[ti], len(witness[ti])
    out = [
        ("status", 0, 0),
        ("depth", 8, v["depth"]),
        ("consumed", 16, v["consumed"]),
        ("case", 24, v["case"]),
        ("terminal_offset", 32, term_off),
        ("terminal_len", 40, term_len),
        ("match_len", 48, v["match_len"]),
    ]
    for i, (kind, nibble, _c) in enumerate(levels):
        base = 128 + 32 * i
        out += [
            (f"rec{i}_offset", base + 0, offs[i]),
            (f"rec{i}_len", base + 8, len(witness[i])),
            (f"rec{i}_kind", base + 16, 0 if kind == "branch" else 1),
            (f"rec{i}_nibble", base + 24, nibble),
        ]
    return out


# ---- insert vectors (mpt_insert .2.4.2.6.2): expected NEW root ------------
# Insert an ABSENT key; expected = the re-rooted trie. Covers the cases the
# first mpt_insert slice supports: EMPTY_TRIE and BRANCH_EMPTY_SLOT (depth 0
# and depth 1 with an extension ancestor).
def vec_mi_branch_empty():
    la = leaf_node([0xa, 0xb], b"v1")
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la)
    root = branch_node(slots)
    val = b"newval"
    new_leaf = leaf_node([0x7, 0x8], val)        # path[consumed+1..] = [7,8]
    slots2 = list(slots)
    slots2[3] = node_ref(new_leaf)               # nibble path[consumed] = 3
    new_root = branch_node(slots2)
    return dict(name="mi_branch_empty", witness=[root], root=trie_root(root),
                path=[0x3, 0x7, 0x8], value=val, expected=trie_root(new_root))


def vec_mi_empty_trie():
    val = b"hello"
    new_root = leaf_node([0x1, 0x2, 0x3, 0x4], val)
    return dict(name="mi_empty_trie", witness=[], root=EMPTY_TRIE_ROOT,
                path=[0x1, 0x2, 0x3, 0x4], value=val,
                expected=trie_root(new_root))


def vec_mi_ext_then_branch():
    la = leaf_node([0xc], b"z" * 40)             # big -> branch hash-referenced
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la)
    branch = branch_node(slots)
    root = extension_node([0x5, 0x6], node_ref(branch))
    val = b"zzz"
    new_leaf = leaf_node([0xc], val)             # path[consumed+1..] = [c]
    slots2 = list(slots)
    slots2[3] = node_ref(new_leaf)               # nibble path[consumed=2] = 3
    new_branch = branch_node(slots2)
    new_root = extension_node([0x5, 0x6], node_ref(new_branch))
    return dict(name="mi_ext_then_branch", witness=[root, branch],
                root=trie_root(root), path=[0x5, 0x6, 0x3, 0xc], value=val,
                expected=trie_root(new_root))


def vec_mi_ext_split():
    """Root = extension prefix [5,6] -> branch. Insert path [5,9,0,0]
    diverges inside the extension at m=1, so the old child stays directly at
    branch slot 6, the new leaf goes under slot 9, and the shared prefix [5]
    wraps the new branch."""
    la = leaf_node([0xa, 0xb], b"x" * 32)
    lb = leaf_node([0xc, 0xd], b"y" * 32)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la)
    slots[2] = node_ref(lb)
    branch = branch_node(slots)
    root = extension_node([0x5, 0x6], node_ref(branch))
    val = b"ext-new"

    new_leaf = leaf_node([0x0, 0x0], val)
    slots2 = [b"\x80"] * 16
    slots2[0x6] = node_ref(branch)
    slots2[0x9] = node_ref(new_leaf)
    split_branch = branch_node(slots2)
    new_root = extension_node([0x5], node_ref(split_branch))
    return dict(name="mi_ext_split", witness=[root], root=trie_root(root),
                path=[0x5, 0x9, 0x0, 0x0], value=val,
                expected=trie_root(new_root))


def vec_mi_leaf_split():
    """Root = leaf key [1,2,3,4]. Insert path [1,2,9,9] (shared prefix [1,2],
    m=2): split into a branch (old leaf' at nibble 3, new leaf at nibble 9)
    wrapped in extension([1,2])."""
    lv = b"leaf-value"
    root = leaf_node([1, 2, 3, 4], lv)
    val = b"newval-xyz"
    old2 = leaf_node([4], lv)          # K[m+1..] = [4]
    new2 = leaf_node([9], val)         # P[m+1..] = [9]
    slots = [b"\x80"] * 16
    slots[3] = node_ref(old2)          # K[m] = 3
    slots[9] = node_ref(new2)          # P[m] = 9
    branch = branch_node(slots)
    newroot = extension_node([1, 2], node_ref(branch))
    return dict(name="mi_leaf_split", witness=[root], root=trie_root(root),
                path=[1, 2, 9, 9], value=val, expected=trie_root(newroot))


def vec_mi_leaf_split_m0():
    """Root = leaf key [5,6,7]. Insert path [9,6,7] diverges at nibble 0
    (m=0): split into a branch directly (no extension wrap)."""
    lv = b"abc"
    root = leaf_node([5, 6, 7], lv)
    val = b"xyz"
    old2 = leaf_node([6, 7], lv)       # K[1..] = [6,7]
    new2 = leaf_node([6, 7], val)      # P[1..] = [6,7]
    slots = [b"\x80"] * 16
    slots[5] = node_ref(old2)          # K[0] = 5
    slots[9] = node_ref(new2)          # P[0] = 9
    branch = branch_node(slots)
    return dict(name="mi_leaf_split_m0", witness=[root], root=trie_root(root),
                path=[9, 6, 7], value=val, expected=trie_root(branch))


def vec_mi_depth2():
    """root branch slot5 -> branch B slot7 -> branch C, slot2 empty. Insert
    path [5,7,2,e] -> BRANCH_EMPTY_SLOT at C, depth 2 (root + B ancestors).
    Exercises the depth>=2 bubble-up."""
    leaf_l = leaf_node([0xd], b"L" * 40)        # >=32 -> hash-ref
    slots_c = [b"\x80"] * 16
    slots_c[0xa] = node_ref(leaf_l)
    c = branch_node(slots_c)
    slots_b = [b"\x80"] * 16
    slots_b[0x7] = node_ref(c)
    b = branch_node(slots_b)
    slots_r = [b"\x80"] * 16
    slots_r[0x5] = node_ref(b)
    root = branch_node(slots_r)
    val = b"depth2val"
    new_leaf = leaf_node([0xe], val)            # path[consumed+1..] = [e]
    slots_c2 = list(slots_c)
    slots_c2[0x2] = node_ref(new_leaf)          # nibble path[consumed=2] = 2
    c2 = branch_node(slots_c2)
    slots_b2 = list(slots_b)
    slots_b2[0x7] = node_ref(c2)
    b2 = branch_node(slots_b2)
    slots_r2 = list(slots_r)
    slots_r2[0x5] = node_ref(b2)
    root2 = branch_node(slots_r2)
    return dict(name="mi_depth2", witness=[root, b, c], root=trie_root(root),
                path=[0x5, 0x7, 0x2, 0xe], value=val, expected=trie_root(root2))


def vec_mi_leafsplit_depth1():
    """R slot5 -> branch B (hash); B slot7 -> leaf LA key [a,b]. Insert path
    [5,7,9,c] diverges at LA (m=0) -> LEAF_SPLIT at DEPTH 1 (ancestors R,B): the
    new branch replaces LA at B slot7, bubbling through B then R. mi_leaf_split
    was depth 0; this exercises the leaf-split terminal under ancestors."""
    la = leaf_node([0xa, 0xb], b"L" * 40)       # >=32 hash-ref
    slots_b = [b"\x80"] * 16
    slots_b[0x7] = node_ref(la)
    b = branch_node(slots_b)
    slots_r = [b"\x80"] * 16
    slots_r[0x5] = node_ref(b)
    root = branch_node(slots_r)
    val = b"newdeep"
    old2 = leaf_node([0xb], b"L" * 40)          # LA[m+1..]=[b]
    new2 = leaf_node([0xc], val)                # P[m+1..]=[c]
    spl = [b"\x80"] * 16
    spl[0xa] = node_ref(old2)
    spl[0x9] = node_ref(new2)
    split_branch = branch_node(spl)
    slots_b2 = list(slots_b)
    slots_b2[0x7] = node_ref(split_branch)
    b2 = branch_node(slots_b2)
    slots_r2 = list(slots_r)
    slots_r2[0x5] = node_ref(b2)
    root2 = branch_node(slots_r2)
    return dict(name="mi_leafsplit_depth1", witness=[root, b, la],
                root=trie_root(root), path=[0x5, 0x7, 0x9, 0xc], value=val,
                expected=trie_root(root2))


def vec_mi_acctkey():
    """Branch root, slot1 empty, slot2 -> leaf. Insert a FULL 64-nibble account
    path (slot1) -> leaf with a 63-nibble (odd) key + a 70-byte account value --
    the realistic case (mi_branch_empty used a 2-nibble key)."""
    other = leaf_node([0x0] * 63, b"O" * 40)
    slots = [b"\x80"] * 16
    slots[2] = node_ref(other)
    root = branch_node(slots)
    path = [1] + [(i * 7 + 3) % 16 for i in range(63)]
    val = bytes.fromhex("f8448080") + b"\x00" * 66
    new_leaf = leaf_node(path[1:], val)
    slots2 = list(slots)
    slots2[1] = node_ref(new_leaf)
    root2 = branch_node(slots2)
    return dict(name="mi_acctkey", witness=[root], root=trie_root(root),
                path=path, value=val, expected=trie_root(root2))


def vec_mi_acctkey_f9():
    """Large branch root with seven occupied slots (payload 241, f8 prefix).
    Insert a full 64-nibble account path into an empty slot, growing the branch
    payload to 273 and forcing the list prefix from f8 LL to f9 LLLL."""
    slots = [b"\x80"] * 16
    for i in range(2, 9):
        slots[i] = node_ref(leaf_node([i] * 63, bytes([i]) * 40))
    root = branch_node(slots)
    path = [1] + [(i * 7 + 3) % 16 for i in range(63)]
    val = bytes.fromhex("f8448080") + b"\x00" * 66
    new_leaf = leaf_node(path[1:], val)
    slots2 = list(slots)
    slots2[1] = node_ref(new_leaf)
    root2 = branch_node(slots2)
    return dict(name="mi_acctkey_f9", witness=[root], root=trie_root(root),
                path=path, value=val, expected=trie_root(root2))


MI_VECTORS = [vec_mi_branch_empty, vec_mi_empty_trie, vec_mi_ext_then_branch,
              vec_mi_ext_split, vec_mi_leaf_split, vec_mi_leaf_split_m0, vec_mi_depth2,
              vec_mi_leafsplit_depth1, vec_mi_acctkey, vec_mi_acctkey_f9]


# ---- insert-aware multi-change driver (mpt_state_root_ins .2.4.2.6.3) ------
def build_state_root_ins_input(root_hash, changes, witness_section) -> bytes:
    """ziskemu -i body for zisk_mpt_state_root_ins (file maps to INPUT+8):
      +8 witness_len | +16 n_changes | +24 root_hash(32B)
      +56 table: N x (path_len:u64, value_len:u64, is_insert:u64)
      then blobs path0,value0,... (each 8-aligned) | then witness."""
    body = bytearray()
    body += struct.pack("<Q", len(witness_section))
    body += struct.pack("<Q", len(changes))
    body += root_hash
    for (path, value, isins) in changes:
        body += struct.pack("<QQQ", len(path), len(value), 1 if isins else 0)
    for (path, value, isins) in changes:
        body += bytes(path)
        while len(body) % 8 != 0:
            body += b"\x00"
        body += value
        while len(body) % 8 != 0:
            body += b"\x00"
    body += witness_section
    while len(body) % 8 != 0:        # ziskemu requires a multiple-of-8 input
        body += b"\x00"
    return bytes(body)


def vec_state_root_ins_large_branch():
    """Large root branch: modify an existing hashed leaf, then insert a full
    64-nibble account into an empty slot of the DB-resident modified root.
    The branch payload crosses the f8 LL -> f9 LLLL boundary after insert."""
    slots = [b"\x80"] * 16
    leaves = {}
    for i in range(2, 9):
        leaf = leaf_node([i] * 63, bytes([i]) * 40)
        leaves[i] = leaf
        slots[i] = node_ref(leaf)
    root = branch_node(slots)
    mod_path = [2] + [2] * 63
    mod_val = b"modified-slot-2-value" * 2
    ins_path = [1] + [(i * 7 + 3) % 16 for i in range(63)]
    ins_val = bytes.fromhex("f8448080") + b"\x00" * 66
    slots2 = list(slots)
    slots2[2] = node_ref(leaf_node([2] * 63, mod_val))
    slots2[1] = node_ref(leaf_node(ins_path[1:], ins_val))
    root2 = branch_node(slots2)
    changes = [(mod_path, mod_val, False), (ins_path, ins_val, True)]
    witness = [root] + [leaves[i] for i in range(2, 9)]
    return dict(name="state_root_ins_large_branch", witness=witness,
                root=trie_root(root), changes=changes, expected=trie_root(root2))

def vec_state_root_ins():
    """Branch root with leaf at slot 1 (existing key A) + empty slot 3.
    change 0 = MODIFY key A; change 1 = INSERT at slot 3. The insert must
    resolve the modified root from the DB (the modify appended it)."""
    la_path = [0xa, 0xb]
    a_old, a_new, v2 = b"A" * 32, b"a-new" * 8, b"v2" * 20
    leaf_a = leaf_node(la_path, a_old)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(leaf_a)
    root = branch_node(slots)
    slots2 = list(slots)
    slots2[1] = node_ref(leaf_node(la_path, a_new))
    slots2[3] = node_ref(leaf_node([0xc, 0xd], v2))
    new_root = branch_node(slots2)
    changes = [([0x1] + la_path, a_new, False), ([0x3, 0xc, 0xd], v2, True)]
    return dict(name="state_root_ins", witness=[root, leaf_a],
                root=trie_root(root), changes=changes,
                expected=trie_root(new_root))


def vec_state_root_ins_longkey():
    """change0 MODIFY key A (slot1) -> R' in DB; change1 INSERT a FULL 64-nibble
    path at R' empty slot3 -> a 63-nibble-key leaf. Combines DB-resident root +
    long account-style leaf key (the real eip4895 precompile case)."""
    a_old, a_new = b"A" * 32, b"a-new" * 8
    leaf_a = leaf_node([0xa, 0xb], a_old)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(leaf_a)
    root = branch_node(slots)
    ipath = [3] + [(i * 5 + 2) % 16 for i in range(63)]   # 64 nibbles at slot3
    val = bytes.fromhex("f8448080") + b"\x00" * 66
    slots2 = list(slots)
    slots2[1] = node_ref(leaf_node([0xa, 0xb], a_new))
    slots2[3] = node_ref(leaf_node(ipath[1:], val))
    new_root = branch_node(slots2)
    changes = [([0x1, 0xa, 0xb], a_new, False), (ipath, val, True)]
    return dict(name="state_root_ins_longkey", witness=[root, leaf_a],
                root=trie_root(root), changes=changes,
                expected=trie_root(new_root))
# ---- insert-aware multi-change driver (mpt_state_root_ins .2.4.2.6.3) ------
def state_root_ins_mode(mode) -> int:
    if isinstance(mode, bool):
        return 1 if mode else 0
    return int(mode)


def build_state_root_ins_input(root_hash, changes, witness_section) -> bytes:
    """ziskemu -i body for zisk_mpt_state_root_ins (file maps to INPUT+8):
      +8 witness_len | +16 n_changes | +24 root_hash(32B)
      +56 table: N x (path_len:u64, value_len:u64, mode:u64)
      then blobs path0,value0,... (each 8-aligned) | then witness.

    Mode values mirror mpt_state_root_ins descriptors: 0=modify, 1=insert,
    2=delete, 3=noop. Historical callers still pass booleans.
    """
    body = bytearray()
    body += struct.pack("<Q", len(witness_section))
    body += struct.pack("<Q", len(changes))
    body += root_hash
    for (path, value, mode) in changes:
        body += struct.pack("<QQQ", len(path), len(value), state_root_ins_mode(mode))
    for (path, value, mode) in changes:
        body += bytes(path)
        while len(body) % 8 != 0:
            body += b"\x00"
        body += value
        while len(body) % 8 != 0:
            body += b"\x00"
    body += witness_section
    while len(body) % 8 != 0:        # ziskemu requires a multiple-of-8 input
        body += b"\x00"
    return bytes(body)


def vec_state_root_ins():
    """Branch root with leaf at slot 1 (existing key A) + empty slot 3.
    change 0 = MODIFY key A; change 1 = INSERT at slot 3. The insert must
    resolve the modified root from the DB (the modify appended it)."""
    la_path = [0xa, 0xb]
    a_old, a_new, v2 = b"A" * 32, b"a-new" * 8, b"v2" * 20
    leaf_a = leaf_node(la_path, a_old)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(leaf_a)
    root = branch_node(slots)
    slots2 = list(slots)
    slots2[1] = node_ref(leaf_node(la_path, a_new))
    slots2[3] = node_ref(leaf_node([0xc, 0xd], v2))
    new_root = branch_node(slots2)
    changes = [([0x1] + la_path, a_new, False), ([0x3, 0xc, 0xd], v2, True)]
    return dict(name="state_root_ins", witness=[root, leaf_a],
                root=trie_root(root), changes=changes,
                expected=trie_root(new_root))


def vec_state_root_ins_deep():
    """R branch: slot1 -> leaf A (existing), slot2 -> branch B (hash); B slot5
    -> leaf B, slot7 empty. change0 = MODIFY key A (slot1) -> R' in the DB;
    change1 = INSERT at B slot7 via path [2,7,e,f] -- descends R' (resolved
    from the DB) -> B (witness) -> empty slot7, so the insert's bubble-up must
    splice a DB-RESIDENT ancestor (R'). This is the depth>=1 insert-after-modify
    the depth-0 state_root_ins vector never exercised."""
    a_old, a_new = b"A" * 32, b"a-new" * 8
    b_old, vins = b"B" * 32, b"ins" * 12
    leaf_a = leaf_node([0xa, 0xb], a_old)
    leaf_b = leaf_node([0xc, 0xd], b_old)
    slots_bb = [b"\x80"] * 16
    slots_bb[0x5] = node_ref(leaf_b)
    bb = branch_node(slots_bb)
    slots_r = [b"\x80"] * 16
    slots_r[0x1] = node_ref(leaf_a)
    slots_r[0x2] = node_ref(bb)
    root = branch_node(slots_r)
    # post: slot1 leaf updated; B gets a new leaf at slot7
    slots_bb2 = list(slots_bb)
    slots_bb2[0x7] = node_ref(leaf_node([0xe, 0xf], vins))
    bb2 = branch_node(slots_bb2)
    slots_r2 = list(slots_r)
    slots_r2[0x1] = node_ref(leaf_node([0xa, 0xb], a_new))
    slots_r2[0x2] = node_ref(bb2)
    root2 = branch_node(slots_r2)
    changes = [([0x1, 0xa, 0xb], a_new, False),
               ([0x2, 0x7, 0xe, 0xf], vins, True)]
    return dict(name="state_root_ins_deep", witness=[root, leaf_a, bb],
                root=trie_root(root), changes=changes,
                expected=trie_root(root2))


def vec_state_root_ins_dbchild():
    """R slot5 -> branch B; B slot5 -> leaf A, slot7 empty. change0 = MODIFY
    key A (path 5,5,a,b) -> re-encodes B AND R into the DB. change1 = INSERT at
    B slot7 (path 5,7,e,f): descends R'(DB) slot5 -> B'(DB, MODIFIED by change0)
    -> empty slot7. So the insert must resolve a DB-modified INTERMEDIATE node
    (B') and bubble through two DB-resident ancestors -- the case neither
    state_root_ins nor state_root_ins_deep exercised."""
    a_old, a_new, vins = b"A" * 32, b"a-new" * 8, b"ins" * 12
    leaf_a = leaf_node([0xa, 0xb], a_old)
    slots_b = [b"\x80"] * 16
    slots_b[0x5] = node_ref(leaf_a)
    bb = branch_node(slots_b)
    slots_r = [b"\x80"] * 16
    slots_r[0x5] = node_ref(bb)
    root = branch_node(slots_r)
    # post
    slots_b2 = list(slots_b)
    slots_b2[0x5] = node_ref(leaf_node([0xa, 0xb], a_new))
    slots_b2[0x7] = node_ref(leaf_node([0xe, 0xf], vins))
    bb2 = branch_node(slots_b2)
    slots_r2 = list(slots_r)
    slots_r2[0x5] = node_ref(bb2)
    root2 = branch_node(slots_r2)
    changes = [([0x5, 0x5, 0xa, 0xb], a_new, False),
               ([0x5, 0x7, 0xe, 0xf], vins, True)]
    return dict(name="state_root_ins_dbchild", witness=[root, bb, leaf_a],
                root=trie_root(root), changes=changes,
                expected=trie_root(root2))


def vec_state_root_ins_delete_noop():
    """Descriptor mode coverage for the post-state trie driver. change0 is a
    no-op, change1 modifies leaf A and places the new root in the DB, and
    change2 deletes leaf B from that DB-resident root. This exercises modes
    3 and 2 in one sequential descriptor run."""
    a_old, b_old, a_new = b"A" * 32, b"B" * 32, b"a-after-noop" * 3
    leaf_a = leaf_node([0xa, 0xb], a_old)
    leaf_b = leaf_node([0xc, 0xd], b_old)
    slots = [b"\x80"] * 16
    slots[0x1] = node_ref(leaf_a)
    slots[0x2] = node_ref(leaf_b)
    root = branch_node(slots)
    root2 = leaf_node([0x1, 0xa, 0xb], a_new)
    changes = [
        ([0x1, 0xa, 0xb], b"ignored-noop-value", 3),
        ([0x1, 0xa, 0xb], a_new, 0),
        ([0x2, 0xc, 0xd], b"", 2),
    ]
    return dict(name="state_root_ins_delete_noop", witness=[root, leaf_a, leaf_b],
                root=trie_root(root), changes=changes, expected=trie_root(root2))


if __name__ == "__main__":
    import os
    outdir = sys.argv[1] if len(sys.argv) > 1 else "gen-out/mpt-set"
    os.makedirs(outdir, exist_ok=True)
    for v in vec_account_add_balance():
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(build_aab_input(v["account"], v["delta"]))
        with open(f"{outdir}/{v['name']}.expected", "w") as f:
            f.write(v["expected"].hex())
        print(f"{v['name']:12} account_len={len(v['account'])} "
              f"new_account={v['expected'].hex()}")
    for v in vec_account_set_uint_field():
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(build_asuf_input(v["account"], v["field_index"], v["value"]))
        with open(f"{outdir}/{v['name']}.expected", "w") as f:
            f.write(v["expected"].hex())
        print(f"{v['name']:12} field={v['field_index']} value={v['value']} "
              f"new_account={v['expected'].hex()}")
    for v in vec_selfdestruct_balance_transfer():
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(build_selfdestruct_balance_input(v["origin"], v["beneficiary"],
                                                     v["same_address"],
                                                     v["created_in_tx"]))
        with open(f"{outdir}/{v['name']}.origin.expected", "w") as f:
            f.write(v["expected_origin"].hex())
        with open(f"{outdir}/{v['name']}.beneficiary.expected", "w") as f:
            f.write(v["expected_beneficiary"].hex())
        print(f"{v['name']:12} same={v['same_address']} created={v['created_in_tx']} "
              f"origin={v['expected_origin'].hex()} "
              f"beneficiary={v['expected_beneficiary'].hex()}")
    for v in vec_bal_account_path():
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(build_bacp_input(v["account_change"]))
        with open(f"{outdir}/{v['name']}.path", "w") as f:
            f.write(v["path"].hex())
        print(f"{v['name']:12} path={v['path'].hex()[:16]}..")
    for v in vec_withdrawal_to_path_delta():
        body = struct.pack("<Q", len(v["wd"])) + v["wd"]
        while len(body) % 8 != 0:
            body += b"\x00"
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(body)
        with open(f"{outdir}/{v['name']}.path", "w") as f:
            f.write(v["path"].hex())
        with open(f"{outdir}/{v['name']}.delta", "w") as f:
            f.write(v["delta"].hex())
        print(f"{v['name']:12} path={v['path'].hex()[:16]}.. delta={v['delta'].hex()}")
    wsr = vec_withdrawals_state_root()
    sec = ssz_section(wsr["witness"])
    with open(f"{outdir}/wsr.input", "wb") as f:
        f.write(build_wsr_input(wsr["root"], wsr["wds"], sec))
    with open(f"{outdir}/wsr.expected", "w") as f:
        f.write(wsr["expected"].hex())
    print(f"{'wsr':12} root={wsr['root'].hex()[:16]}.. "
          f"post_state_root={wsr['expected'].hex()} (n_wd={len(wsr['wds'])})")
    for mk in VECTORS:
        v = mk()
        sec = ssz_section(v["witness"])
        inp = build_probe_input(v["root"], v["path"], v["new_value"], sec)
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(inp)
        with open(f"{outdir}/{v['name']}.expected", "w") as f:
            f.write(v["expected"].hex())
        # record-walk expectation: "<name> <output_byte_offset> <u64_value>"
        rw = record_walk_expected(v)
        with open(f"{outdir}/{v['name']}.rwexpected", "w") as f:
            for name, off, val in rw:
                f.write(f"{name} {off} {val}\n")
        depth = next(val for nm, _o, val in rw if nm == "depth")
        print(f"{v['name']:12} root={v['root'].hex()[:16]}.. "
              f"new_root={v['expected'].hex()[:16]}.. rw_depth={depth}")
    # insert-walk divergence vectors (mpt_insert_walk)
    for mk in IW_VECTORS:
        v = mk()
        sec = ssz_section(v["witness"])
        inp = build_probe_input(v["root"], v["path"], b"", sec)
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(inp)
        iw = insert_walk_expected(v)
        with open(f"{outdir}/{v['name']}.iwexpected", "w") as f:
            for name, off, val in iw:
                f.write(f"{name} {off} {val}\n")
        print(f"{v['name']:24} case={v['case']} depth={v['depth']} "
              f"consumed={v['consumed']} match_len={v['match_len']}")
    # insert vectors (mpt_insert): expected NEW root
    for mk in MI_VECTORS:
        v = mk()
        sec = ssz_section(v["witness"])
        inp = build_probe_input(v["root"], v["path"], v["value"], sec)
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(inp)
        with open(f"{outdir}/{v['name']}.expected", "w") as f:
            f.write(v["expected"].hex())
        print(f"{v['name']:24} root={v['root'].hex()[:16]}.. "
              f"new_root={v['expected'].hex()}")
    # accumulating 2-update vector (mpt_set_acc)
    a = vec_acc()
    sec = ssz_section(a["witness"])
    inp = build_acc_probe_input(a["root"], a["path1"], a["value1"],
                                a["path2"], a["value2"], sec)
    with open(f"{outdir}/acc.input", "wb") as f:
        f.write(inp)
    with open(f"{outdir}/acc.expected", "w") as f:
        f.write(a["expected"].hex())
    print(f"{'acc':12} root={a['root'].hex()[:16]}.. "
          f"final_root={a['expected'].hex()}")
    # multi-change driver vector (mpt_state_root)
    sr = vec_state_root()
    sec = ssz_section(sr["witness"])
    inp = build_state_root_input(sr["root"], sr["changes"], sec)
    with open(f"{outdir}/state_root.input", "wb") as f:
        f.write(inp)
    with open(f"{outdir}/state_root.expected", "w") as f:
        f.write(sr["expected"].hex())
    print(f"{'state_root':12} root={sr['root'].hex()[:16]}.. "
          f"final_root={sr['expected'].hex()} (n={len(sr['changes'])})")
    # insert-aware multi-change driver vector (mpt_state_root_ins)
    sri = vec_state_root_ins()
    sec = ssz_section(sri["witness"])
    with open(f"{outdir}/state_root_ins.input", "wb") as f:
        f.write(build_state_root_ins_input(sri["root"], sri["changes"], sec))
    with open(f"{outdir}/state_root_ins.expected", "w") as f:
        f.write(sri["expected"].hex())
    print(f"{'state_root_ins':12} root={sri['root'].hex()[:16]}.. "
          f"final_root={sri['expected'].hex()} (modify+insert)")
    srilk = vec_state_root_ins_longkey()
    sec = ssz_section(srilk["witness"])
    with open(f"{outdir}/state_root_ins_longkey.input", "wb") as f:
        f.write(build_state_root_ins_input(srilk["root"], srilk["changes"], sec))
    with open(f"{outdir}/state_root_ins_longkey.expected", "w") as f:
        f.write(srilk["expected"].hex())
    print(f"{'sri_longkey':12} final_root={srilk['expected'].hex()} (DB root + 64-nibble insert)")
    srilb = vec_state_root_ins_large_branch()
    sec = ssz_section(srilb["witness"])
    with open(f"{outdir}/state_root_ins_large_branch.input", "wb") as f:
        f.write(build_state_root_ins_input(srilb["root"], srilb["changes"], sec))
    with open(f"{outdir}/state_root_ins_large_branch.expected", "w") as f:
        f.write(srilb["expected"].hex())
    print(f"{'sri_large':12} final_root={srilb['expected'].hex()} (large DB root + insert)")
    srid = vec_state_root_ins_deep()
    sec = ssz_section(srid["witness"])
    with open(f"{outdir}/state_root_ins_deep.input", "wb") as f:
        f.write(build_state_root_ins_input(srid["root"], srid["changes"], sec))
    with open(f"{outdir}/state_root_ins_deep.expected", "w") as f:
        f.write(srid["expected"].hex())
    print(f"{'sri_deep':12} root={srid['root'].hex()[:16]}.. "
          f"final_root={srid['expected'].hex()} (modify+insert depth>=1)")
    sridc = vec_state_root_ins_dbchild()
    sec = ssz_section(sridc["witness"])
    with open(f"{outdir}/state_root_ins_dbchild.input", "wb") as f:
        f.write(build_state_root_ins_input(sridc["root"], sridc["changes"], sec))
    with open(f"{outdir}/state_root_ins_dbchild.expected", "w") as f:
        f.write(sridc["expected"].hex())
    print(f"{'sri_dbchild':12} root={sridc['root'].hex()[:16]}.. "
          f"final_root={sridc['expected'].hex()} (insert via DB-modified child)")
    sridn = vec_state_root_ins_delete_noop()
    sec = ssz_section(sridn["witness"])
    with open(f"{outdir}/state_root_ins_delete_noop.input", "wb") as f:
        f.write(build_state_root_ins_input(sridn["root"], sridn["changes"], sec))
    with open(f"{outdir}/state_root_ins_delete_noop.expected", "w") as f:
        f.write(sridn["expected"].hex())
    print(f"{'sri_del_noop':12} root={sridn['root'].hex()[:16]}.. "
          f"final_root={sridn['expected'].hex()} (noop+modify+delete)")
