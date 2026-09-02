#!/usr/bin/env python3
"""Check the two-stage wrapper/direct-JAL vacuity signature (#12747).

The first stage is structural.  Among witnessed ``.conditional`` rows, find a
whole-routine ``cpsTripleWithin`` whose ``CodeReq`` resolves to
``CodeReq.ofProg`` at the row's linked entry, and whose Program contains a
direct ``JAL .x1`` to a different ``GuestAddrs`` entry.  Such a call is not
covered by the wrapper's own image.

The structural signature is deliberately not the final finding.  A registered
domain can force an early branch before the external call, as happens for the
empty-section controls in this repository.  The second stage therefore runs a
small, conservative abstract interpreter over the *actual registered
precondition* and the Program's direct control-flow.  It tracks only facts
that are explicit in that precondition: zero/nonzero register values and
zero-valued named memory cells.  It does not infer semantic facts from prose.
If the interpreter cannot parse the required shape, the result is ``unknown``
and the gate fails closed.

The current four-row regression fixture is:

* ``eip7702_authorization_signing_hash`` and ``stage_system_call``: reachable;
* ``blockhash_from_witness_headers`` and ``witness_codes_lookup_by_hash``:
  gated away by their registered empty-domain preconditions.

The structural scan can also see call-bearing routines that are not this
defect: a full inline arm can have direct calls without any residual callee
contract.  The residual-telescope check reports that third category instead
of treating every direct call as a vacuity finding.  The arm-qualified theorem
name is reported mechanically as an ``inline-arm`` control; on current main
this explicitly excludes K70's ``header_validate_excess_blob_gas`` arm.

This is a lower-bound detector.  It sees direct ``JAL`` syntax in checked-in
Programs and cannot see indirect ``JALR`` calls, dispatch/jump tables,
generated or runtime-constructed strings, or aliases/unions that do not
resolve to an ``ofProg`` spine.  Those limits are printed by the live check;
they are not silently treated as evidence of safety.

Usage:
  python3 scripts/check-wrapper-jal-vacuity.py --self-test
  python3 scripts/check-wrapper-jal-vacuity.py
"""

from __future__ import annotations

from dataclasses import dataclass
import re
import subprocess
import sys
from collections import deque
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ROUTINES = ROOT / "EvmAsm" / "Progress" / "Routines.lean"
GUEST_ADDRS = ROOT / "EvmAsm" / "Codegen" / "GuestAddrs.lean"

EXPECTED = {
    "blockhash_from_witness_headers": "gated-away",
    "witness_codes_lookup_by_hash": "gated-away",
    "stage_system_call": "reachable",
    "eip7702_authorization_signing_hash": "reachable",
}

# These are regression controls, not a claim that future rows are harmless.
# A new structural match must be reviewed and classified before it can pass.
EXPECTED_REFS = {
    "blockhash_from_witness_headers":
        "blockhash_from_witness_headers_spec_within_empty_section",
    "witness_codes_lookup_by_hash":
        "witness_codes_lookup_by_hash_spec_within_empty_section",
    "stage_system_call": "stage_system_call_spec_within",
    "eip7702_authorization_signing_hash":
        "eip7702_authorization_signing_hash_spec_within",
}

REF_RE = re.compile(r'\(some\s+"([^"]+)"\)')
DEF_HEAD = re.compile(
    r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:abbrev|def)\s+([A-Za-z_][A-Za-z0-9_']*)")
IDENT = re.compile(r"(?<![\w'!?.])[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*")

OPENERS = "([{⟨"
CLOSERS = ")]}⟩"

HISTORICAL_CENSUS_SHA = "8a0fbf3e88f7244a3393384f53e2dd97df5d2156"

# Definitions that are not useful to resolving a CodeReq or a precondition,
# and whose expansion would make the source-level check needlessly enormous.
NO_EXPAND = {
    "CodeReq", "GuestAddrs", "BitVec", "List", "Option", "Word", "Reg",
    "Instr", "Assertion", "cpsTripleWithin", "regsAt", "regsOwnAt",
    "frameSlotsOwn", "frameSlotsSaved", "stackFree", "bytesRegion",
    "sepConj", "empAssertion", "pcFree", "Program", "Fn",
}


@dataclass(frozen=True)
class Row:
    symbol: str
    tier: str
    ref: str | None
    gate: str


@dataclass(frozen=True)
class Decl:
    name: str
    path: Path
    line: int
    body: str


@dataclass(frozen=True)
class Instruction:
    index: int
    op: str
    rest: str
    line: int


@dataclass(frozen=True)
class Call:
    index: int
    target: str
    line: int


@dataclass(frozen=True)
class Branch:
    kind: str
    left: int
    right: int
    target: int
    line: int


@dataclass(frozen=True)
class AbsState:
    zero: frozenset[int]
    nonzero: frozenset[int]
    labels: tuple[tuple[int, str], ...]
    memzero: frozenset[str]
    expr: tuple[tuple[int, str], ...] = ()

    def label_map(self) -> dict[int, str]:
        return dict(self.labels)

    def expr_map(self) -> dict[int, str]:
        return dict(self.expr)


@dataclass(frozen=True)
class Analysis:
    status: str
    calls: tuple[Call, ...]
    reached: tuple[Call, ...]
    evidence: tuple[str, ...]
    residual: bool = False


def scan_top_level(text: str, needle: str) -> int | None:
    depth = 0
    i = 0
    while i < len(text):
        c = text[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(needle, i):
            return i
        i += 1
    return None


def split_app_args(text: str) -> list[str]:
    out: list[str] = []
    cur: list[str] = []
    depth = 0
    for c in text:
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        if c.isspace() and depth == 0:
            if cur:
                out.append("".join(cur))
                cur = []
        else:
            cur.append(c)
    if cur:
        out.append("".join(cur))
    return out


def declaration_bodies(path: Path, text: str) -> list[Decl]:
    """Read top-level def/abbrev bodies without trying to parse Lean."""
    matches = list(DEF_HEAD.finditer(text))
    out: list[Decl] = []
    for k, match in enumerate(matches):
        end = (matches[k + 1].start() if k + 1 < len(matches) else len(text))
        # A column-zero comment/docstring ends the preceding declaration's
        # body.  This also prevents a later declaration from being swallowed.
        boundary = re.search(r"(?m)^\S", text[match.end():end])
        chunk_end = match.end() + (boundary.start() if boundary else end - match.end())
        chunk = text[match.end():chunk_end]
        eq = chunk.find(":=")
        if eq is None or eq < 0:
            continue
        out.append(Decl(match.group(1), path,
                        text.count("\n", 0, match.start()) + 1,
                        chunk[eq + 2:]))
    return out


class Resolver:
    def __init__(self, decls: list[Decl]):
        self.by_name: dict[str, list[Decl]] = {}
        self.by_path: dict[Path, dict[str, list[Decl]]] = {}
        for decl in decls:
            self.by_name.setdefault(decl.name, []).append(decl)
            self.by_path.setdefault(decl.path, {}).setdefault(decl.name, []).append(decl)

    def _decl(self, name: str, owner: Path) -> Decl | None:
        local = self.by_path.get(owner, {}).get(name, [])
        if len(local) == 1:
            return local[0]
        global_defs = self.by_name.get(name, [])
        if len(global_defs) == 1:
            return global_defs[0]
        return None

    def expand_name(self, name: str, owner: Path,
                    stack: tuple[tuple[str, Path], ...] = ()) -> str | None:
        if name in NO_EXPAND or name.endswith("_prog"):
            return None
        if (name, owner) in stack or len(stack) >= 10:
            return None
        decl = self._decl(name, owner)
        if decl is None or len(decl.body) > 5000:
            return None
        return self.expand(decl.body, decl.path, stack + ((name, owner),))

    def expand(self, text: str, owner: Path,
               stack: tuple[tuple[str, Path], ...] = ()) -> str:
        value = text
        for _ in range(8):
            changed = False

            def replace(match: re.Match[str]) -> str:
                nonlocal changed
                token = match.group(0)
                # Namespaces and field notation are syntax we must preserve;
                # only bare aliases are candidates for textual expansion.
                if "." in token or token in NO_EXPAND or token.endswith("_prog"):
                    return token
                replacement = self.expand_name(token, owner, stack)
                if replacement is None or len(value) + len(replacement) > 24000:
                    return token
                changed = True
                return "(" + replacement + ")"

            new_value = IDENT.sub(replace, value)
            value = new_value
            if not changed:
                break
        return value


def extract_field(block: str, field: str) -> str:
    marker = "(" + field
    start = block.find(marker)
    if start < 0:
        return ""
    # Field expressions in the registry contain strings and `++`, but no
    # nested parenthesized propositions.  Scan balanced parentheses anyway so
    # this fails closed if that convention changes.
    depth = 0
    quote = False
    escaped = False
    for i in range(start, len(block)):
        c = block[i]
        if quote:
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                quote = False
            continue
        if c == '"':
            quote = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return block[start + 1:i]
    return ""


def quoted_text(expr: str) -> str:
    pieces = re.findall(r'"((?:\\.|[^"\\])*)"', expr)
    return "".join(bytes(piece, "utf-8").decode("unicode_escape") for piece in pieces)


def rows(text: str) -> list[Row]:
    out: list[Row] = []
    chunks = re.split(r'(?m)^  routine "', text)[1:]
    for chunk in chunks:
        match = re.match(r'([A-Za-z0-9_]+)"\s+\.(\w+)', chunk)
        if not match:
            continue
        block = '"' + chunk
        ref_match = REF_RE.search(block)
        out.append(Row(match.group(1), match.group(2),
                       ref_match.group(1) if ref_match else None,
                       quoted_text(extract_field(block, "gate"))))
    return out


def theorem_statement(text: str, theorem: str) -> str | None:
    match = re.search(r"(?m)^\s*theorem\s+" + re.escape(theorem) + r"\b", text)
    if match is None:
        return None
    rest = text[match.end():]
    cut = re.search(r":=\s*by\b|:=\s*\n|:=\s*$", rest)
    return rest[:cut.start()] if cut else rest


def conclusion(statement: str) -> str | None:
    index = scan_top_level(statement, ":")
    return None if index is None else " ".join(statement[index + 1:].split())


def candidate_args(statement: str) -> list[str] | None:
    concl = conclusion(statement)
    if concl is None or "cpsTripleWithin" not in concl:
        return None
    app = concl[concl.index("cpsTripleWithin"):]
    args = split_app_args(app)
    return args if len(args) >= 7 else None


def all_sources() -> tuple[list[Decl], dict[Path, str]]:
    decls: list[Decl] = []
    texts: dict[Path, str] = {}
    for path in sorted((ROOT / "EvmAsm").glob("**/*.lean")):
        text = path.read_text(errors="replace")
        texts[path] = text
        decls.extend(declaration_bodies(path, text))
    return decls, texts


def find_theorem(ref: str, texts: dict[Path, str]) -> tuple[Path, str] | None:
    hits: list[tuple[Path, str]] = []
    for path, text in texts.items():
        if "EvmAsm/Progress/" in str(path):
            continue
        if re.search(r"(?m)^\s*theorem\s+" + re.escape(ref) + r"\b", text):
            hits.append((path, text))
    return hits[0] if len(hits) == 1 else None


def strip_outer(token: str) -> str:
    token = token.strip()
    while token.startswith("(") and token.endswith(")"):
        depth = 0
        balanced = True
        for i, c in enumerate(token):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i != len(token) - 1:
                    balanced = False
                    break
        if balanced:
            token = token[1:-1].strip()
        else:
            break
    return token


def of_prog(resolved: str) -> tuple[str, str] | None:
    expression = strip_outer(resolved.strip())
    match = re.match(r"CodeReq\.ofProg\b(.*)$", expression, re.S)
    if match is None:
        return None
    args = split_app_args(match.group(1).strip())
    if len(args) < 2:
        return None
    return strip_outer(args[0]), strip_outer(args[1])


def anchored_symbol(base: str) -> str | None:
    matches = re.findall(r"GuestAddrs\.([A-Za-z_][A-Za-z0-9_]*)", base)
    return matches[0] if len(matches) == 1 else None


def guest_address_values() -> dict[str, int]:
    """Read numeric linked addresses used to test the actual image interval."""
    values: dict[str, int] = {}
    pattern = re.compile(
        r"(?m)^def\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*Nat\s*:=\s*"
        r"(0x[0-9A-Fa-f]+|[0-9]+)\s*$")
    for match in pattern.finditer(GUEST_ADDRS.read_text(errors="replace")):
        values[match.group(1)] = int(match.group(2), 0)
    return values


def parse_program(decl: Decl) -> tuple[list[Instruction], list[str]]:
    instructions: list[Instruction] = []
    warnings: list[str] = []
    for offset, line in enumerate(decl.body.splitlines()):
        match = re.match(r"^\s*(?:\[\s*)?\.([A-Z][A-Z0-9_]*)\b(.*)$", line)
        if not match:
            continue
        rest = match.group(2).strip().rstrip(",").rstrip("]").strip()
        instructions.append(Instruction(len(instructions), match.group(1), rest,
                                        decl.line + offset))
    if not instructions:
        warnings.append(f"{decl.name}: no instruction lines parsed")
    return instructions, warnings


def parse_calls(instructions: list[Instruction]) -> tuple[list[Call], list[str]]:
    calls: list[Call] = []
    warnings: list[str] = []
    for ins in instructions:
        if ins.op != "JAL" or not re.search(r"\.x1\b", ins.rest):
            continue
        match = re.search(
            r"jalOff\s+GuestAddrs\.([A-Za-z_][A-Za-z0-9_]*)\s+",
            ins.rest)
        if match is None:
            warnings.append(f"line {ins.line}: direct JAL target not parsed")
            continue
        calls.append(Call(ins.index, match.group(1), ins.line))
    return calls, warnings


def parse_target(rest: str, ins: Instruction, width: int,
                 current_symbol: str) -> int | None:
    match = re.search(
        r"brOff\s*\(\s*GuestAddrs\.[A-Za-z_][A-Za-z0-9_]*\s*\+\s*(\d+)\s*\)"
        r"\s*\(\s*GuestAddrs\.[A-Za-z_][A-Za-z0-9_]*\s*\+\s*(\d+)\s*\)",
        rest)
    if match:
        target, source = (int(match.group(1)) // 4,
                          int(match.group(2)) // 4)
        if source != ins.index:
            return None
        return target
    match = re.search(r"\(\s*(-?\d+)\s*:\s*BitVec\s+" + str(width) + r"\s*\)", rest)
    if match:
        delta = int(match.group(1))
        if delta % 4:
            return None
        return ins.index + delta // 4
    return None


def parse_branches(instructions: list[Instruction], symbol: str) -> tuple[dict[int, Branch], dict[int, int], list[str]]:
    branches: dict[int, Branch] = {}
    jumps: dict[int, int] = {}
    warnings: list[str] = []
    for ins in instructions:
        if ins.op in {"BEQ", "BNE", "BLTU", "BGEU"}:
            regs = re.findall(r"\.x(\d+)", ins.rest[:ins.rest.find("(")])
            if len(regs) != 2:
                warnings.append(f"line {ins.line}: {ins.op} registers not parsed")
                continue
            target = parse_target(ins.rest, ins, 13, symbol)
            if target is None:
                warnings.append(f"line {ins.line}: {ins.op} target not parsed")
                continue
            branches[ins.index] = Branch(ins.op, int(regs[0]), int(regs[1]),
                                         target, ins.line)
        elif ins.op == "JAL" and re.search(r"\.x0\b", ins.rest):
            target = parse_target(ins.rest, ins, 21, symbol)
            if target is not None:
                jumps[ins.index] = target
            elif "jalOff" in ins.rest:
                match = re.search(
                    r"jalOff\s*\(\s*GuestAddrs\.[A-Za-z_][A-Za-z0-9_]*\s*\+\s*(\d+)\s*\)"
                    r"\s*\(\s*GuestAddrs\.[A-Za-z_][A-Za-z0-9_]*\s*\+\s*(\d+)\s*\)",
                    ins.rest)
                if match and int(match.group(2)) // 4 == ins.index:
                    jumps[ins.index] = int(match.group(1)) // 4
                else:
                    warnings.append(f"line {ins.line}: internal JAL target not parsed")
    return branches, jumps, warnings


def zero_facts(pre: str, labels: set[str]) -> tuple[set[int], set[str]]:
    zero_regs = {0}
    for match in re.finditer(
        r"\.x(\d+)[^\n*]{0,120}↦ᵣ\s*\(\s*0\s*:\s*Word", pre):
        zero_regs.add(int(match.group(1)))
    # Alias definitions expand through line breaks (for example
    # ``((GuestAddrs.wcidx_enabled : Word) ↦ₘ 0)``).  Normalize whitespace
    # before looking for the adjacent memory assertion; otherwise a harmless
    # pretty-printing change makes the domain fact disappear.
    flat_pre = re.sub(r"\s+", " ", pre)
    memzero: set[str] = set()
    for label in labels:
        pattern = (r"(?:GuestAddrs\.)?" + re.escape(label) +
                   r"\b[^*]{0,120}?↦ₘ\s*\(\s*0\s*:\s*Word")
        if re.search(pattern, flat_pre):
            memzero.add(label)
    return zero_regs, memzero


def normalize_expr(expr: str) -> str:
    return re.sub(r"\s+", "", expr).replace("(", "").replace(")", "")


def static_ult_facts(statement: str) -> tuple[tuple[str, str, bool], ...]:
    """Extract only explicit unsigned-ult hypotheses from a theorem type."""
    facts: list[tuple[str, str, bool]] = []
    # The facts in the registry theorem telescopes are simple expressions.  A
    # nested expression is intentionally not guessed: it remains unknown and
    # the gate fails closed.
    pattern = (r"(?P<neg>¬\s*)?BitVec\.ult\s*\(\s*([^()]*)\s*\)\s+"
               r"([A-Za-z_][A-Za-z0-9_]*|\d+)\s*=\s*true")
    for match in re.finditer(pattern, statement):
        left = normalize_expr(match.group(2))
        right = normalize_expr(match.group(3))
        if left and right:
            # The one named target in the current K70 theorem is definitionally
            # the LUI immediate emitted by the branch comparison.
            if right == "k70Target":
                right = "lui:448"
            facts.append((left, right, match.group("neg") is None))
    return tuple(facts)


def register_expr_facts(pre: str) -> dict[int, str]:
    """Read simple register-to-parameter equalities from the precondition."""
    flat_pre = re.sub(r"\s+", " ", pre)
    expr: dict[int, str] = {0: "0"}
    pattern = r"\.x(\d+)\b[^*]{0,120}?↦ᵣ\s*(?:\(\s*)?([A-Za-z_][A-Za-z0-9_]*|\d+)"
    for match in re.finditer(pattern, flat_pre):
        expr[int(match.group(1))] = normalize_expr(match.group(2))
    return expr


def known_relation(op: str, left: int, right: int,
                   zero: set[int], nonzero: set[int],
                   expr: dict[int, str],
                   ult_facts: tuple[tuple[str, str, bool], ...]) -> bool | None:
    if op in {"BLTU", "BGEU"}:
        left_expr = normalize_expr(expr.get(left, ""))
        right_expr = normalize_expr(expr.get(right, ""))
        if not left_expr or not right_expr:
            return None
        for fact_left, fact_right, value in ult_facts:
            if op == "BLTU" and (left_expr, right_expr) == (fact_left, fact_right):
                return value
            if op == "BGEU" and (right_expr, left_expr) == (fact_left, fact_right):
                return not value
        return None
    if left in zero and right in zero:
        equal = True
    elif (left in zero and right in nonzero) or (right in zero and left in nonzero):
        equal = False
    else:
        return None
    return equal if op == "BEQ" else not equal


def parse_imm(rest: str) -> int | None:
    match = re.search(
        r"\(\s*(-?\d+)\s*:\s*(?:Word|BitVec\s+\d+)\s*\)", rest)
    return int(match.group(1)) if match else None


def regs_in(rest: str) -> list[int]:
    return [int(x) for x in re.findall(r"\.x(\d+)", rest)]


def update_state(state: AbsState, ins: Instruction) -> AbsState:
    zero = set(state.zero)
    nonzero = set(state.nonzero)
    labels = state.label_map()
    memzero = set(state.memzero)
    expr = state.expr_map()

    if ins.op in {"BEQ", "BNE", "BLTU", "BGEU", "JALR"}:
        if ins.op == "JALR":
            regs = regs_in(ins.rest)
            if regs:
                dest = regs[0]
                if dest != 0:
                    zero.discard(dest)
                    nonzero.discard(dest)
                    labels.pop(dest, None)
                    expr.pop(dest, None)
        return AbsState(frozenset(zero), frozenset(nonzero),
                        tuple(sorted(labels.items())), frozenset(memzero),
                        tuple(sorted(expr.items())))

    regs = regs_in(ins.rest)
    if not regs:
        return state

    dest = regs[0]
    if dest == 0:
        return state

    def set_unknown(reg: int) -> None:
        zero.discard(reg)
        nonzero.discard(reg)
        labels.pop(reg, None)
        expr.pop(reg, None)

    if ins.op == "MV" and len(regs) >= 2:
        src = regs[1]
        if src in zero:
            zero.add(dest); nonzero.discard(dest)
        elif src in nonzero:
            nonzero.add(dest); zero.discard(dest)
        else:
            set_unknown(dest)
        if src in labels:
            labels[dest] = labels[src]
        else:
            labels.pop(dest, None)
        if src in expr:
            expr[dest] = expr[src]
        else:
            expr.pop(dest, None)
    elif ins.op == "LI":
        imm = parse_imm(ins.rest)
        if imm == 0:
            zero.add(dest); nonzero.discard(dest)
        elif imm is not None:
            nonzero.add(dest); zero.discard(dest)
        else:
            set_unknown(dest)
        labels.pop(dest, None)
        if imm is not None:
            expr[dest] = str(imm)
        else:
            expr.pop(dest, None)
    elif ins.op == "AUIPC":
        set_unknown(dest)
        match = re.search(r"GuestAddrs\.([A-Za-z_][A-Za-z0-9_]*)", ins.rest)
        if match:
            labels[dest] = match.group(1)
        expr.pop(dest, None)
    elif ins.op == "LUI":
        imm = parse_imm(ins.rest)
        set_unknown(dest)
        if imm is not None:
            expr[dest] = f"lui:{imm}"
    elif ins.op in {"ADD", "SUB"} and len(regs) >= 3:
        left_expr = expr.get(regs[1])
        right_expr = expr.get(regs[2])
        set_unknown(dest)
        if left_expr is not None and right_expr is not None:
            op = "+" if ins.op == "ADD" else "-"
            expr[dest] = normalize_expr(f"{left_expr}{op}{right_expr}")
        else:
            set_unknown(dest)
    elif ins.op == "ADDI" and len(regs) >= 2:
        src = regs[1]
        src_label = labels.get(src)
        imm = parse_imm(ins.rest)
        if imm == 0 and src in zero:
            zero.add(dest); nonzero.discard(dest)
        elif imm == 0 and src in nonzero:
            nonzero.add(dest); zero.discard(dest)
        else:
            set_unknown(dest)
        # The two-instruction `la` idiom carries a symbolic address through
        # the ADDI even though its low immediate is not a numeric Word.
        if src_label is not None and "laLo" in ins.rest:
            labels[dest] = src_label
        elif dest not in labels:
            labels.pop(dest, None)
        if imm is not None and src in expr:
            expr[dest] = normalize_expr(f"{expr[src]}+{imm}")
        elif "laLo" not in ins.rest:
            expr.pop(dest, None)
    elif ins.op in {"LD", "LW", "LWU", "LH", "LHU", "LB", "LBU"} and len(regs) >= 2:
        base = regs[1]
        offset = parse_imm(ins.rest)
        if offset == 0 and labels.get(base) in memzero:
            zero.add(dest); nonzero.discard(dest)
            expr[dest] = "0"
        else:
            set_unknown(dest)
        labels.pop(dest, None)
    elif ins.op == "SD" and len(regs) >= 2:
        src, base = regs[0], regs[1]
        offset = parse_imm(ins.rest)
        if offset == 0 and labels.get(base):
            label = labels[base]
            if src in zero:
                memzero.add(label)
            else:
                memzero.discard(label)
        # SD has no destination register.
        return AbsState(frozenset(zero), frozenset(nonzero),
                        tuple(sorted(labels.items())), frozenset(memzero),
                        tuple(sorted(expr.items())))
    else:
        set_unknown(dest)

    return AbsState(frozenset(zero), frozenset(nonzero),
                    tuple(sorted(labels.items())), frozenset(memzero),
                    tuple(sorted(expr.items())))


def analyze(instructions: list[Instruction], calls: list[Call],
            branches: dict[int, Branch], jumps: dict[int, int],
            pre: str, symbol: str, statement: str = "",
            residual: bool = False) -> Analysis:
    labels = set()
    for ins in instructions:
        labels.update(re.findall(r"GuestAddrs\.([A-Za-z_][A-Za-z0-9_]*)", ins.rest))
    initial_zero, initial_memzero = zero_facts(pre, labels)
    initial = AbsState(frozenset(initial_zero), frozenset(), tuple(),
                       frozenset(initial_memzero),
                       tuple(sorted(register_expr_facts(pre).items())))
    ult_facts = static_ult_facts(statement)
    by_index = {call.index: call for call in calls}
    reached: dict[int, Call] = {}
    evidence: list[str] = []
    queue = deque([(0, initial)])
    seen: set[tuple[int, AbsState]] = set()
    uncertain = False
    while queue:
        index, state = queue.popleft()
        key = (index, state)
        if key in seen:
            continue
        seen.add(key)
        if len(seen) > 1024:
            uncertain = True
            evidence.append("abstract state limit exceeded")
            break
        if index < 0 or index >= len(instructions):
            # Falling off the list is not a valid return path.  It matters
            # only if this was the result of an unparsed transfer.
            uncertain = True
            evidence.append(f"control-flow target {index} is outside Program")
            continue
        ins = instructions[index]
        if index in by_index:
            reached[index] = by_index[index]
            evidence.append(
                f"direct JAL to {by_index[index].target} at instruction {index} "
                f"(+{index * 4} bytes)")

        if ins.op in {"BEQ", "BNE", "BLTU", "BGEU"}:
            branch = branches.get(index)
            if branch is None:
                uncertain = True
                continue
            relation = known_relation(branch.kind, branch.left, branch.right,
                                      set(state.zero), set(state.nonzero),
                                      state.expr_map(), ult_facts)
            next_states: list[int]
            if relation is True:
                next_states = [branch.target]
            elif relation is False:
                next_states = [index + 1]
            else:
                next_states = [index + 1, branch.target]
            for target in next_states:
                queue.append((target, state))
            continue
        if ins.op == "JAL" and re.search(r"\.x0\b", ins.rest):
            target = jumps.get(index)
            if target is None:
                uncertain = True
                continue
            queue.append((target, state))
            continue
        if ins.op == "JALR":
            regs = regs_in(ins.rest)
            # The ordinary `jalr x0, x1, 0` is the routine return.
            if len(regs) >= 2 and regs[0] == 0 and regs[1] == 1:
                continue
            uncertain = True
            evidence.append(f"unresolved JALR at instruction {index}")
            continue
        next_state = update_state(state, ins)
        queue.append((index + 1, next_state))

    if uncertain:
        status = "unknown"
    elif reached:
        status = "reachable"
    else:
        status = "gated-away"
    return Analysis(status, tuple(calls), tuple(reached.values()),
                    tuple(evidence), residual)


def has_residual_hypothesis(statement: str, resolver: Resolver,
                            theorem_path: Path) -> bool:
    """Detect a callee-contract premise in the theorem telescope.

    The wrapper-JAL defect is about a residual hypothesis standing in for a
    callee contract.  A direct-call Program without such a premise is merely
    a call-bearing routine (for example K70's inline arm), not this defect.
    Resolve only names whose convention denotes a call shape/contract; a full
    theorem-type expansion would make this source check both slow and brittle.
    """
    conclusion_colon = scan_top_level(statement, ":")
    telescope = statement if conclusion_colon is None else statement[:conclusion_colon]
    if "cpsTripleWithin" in telescope or "cpsCallWithin" in telescope:
        return True
    for token in IDENT.findall(telescope):
        if not (token.endswith("CallShape") or token.endswith("Contract")):
            continue
        body = resolver.expand_name(token, theorem_path)
        if body is not None and ("cpsTripleWithin" in body or
                                 "cpsCallWithin" in body):
            return True
    return False


def partition_external_targets(base: str, instruction_count: int,
                                calls: list[Call],
                                addresses: dict[str, int]) -> tuple[list[Call], list[str]]:
    """Partition direct calls by the numeric ``CodeReq.ofProg`` interval."""
    base_value = addresses.get(base)
    if base_value is None:
        return [], [f"linked base {base} has no numeric GuestAddrs value"]
    image_end = base_value + 4 * instruction_count
    outside: list[Call] = []
    problems: list[str] = []
    for call in calls:
        target_value = addresses.get(call.target)
        if target_value is None:
            problems.append(
                f"JAL target {call.target} has no numeric GuestAddrs value")
        elif base_value <= target_value < image_end:
            continue
        else:
            outside.append(call)
    return outside, problems


def inspect_row(row: Row, theorem_path: Path, theorem_text: str,
                resolver: Resolver, decls: list[Decl],
                addresses: dict[str, int]) -> tuple[bool, str, Analysis | None, str]:
    statement = theorem_statement(theorem_text, row.ref or "")
    if statement is None:
        return False, "theorem declaration not found", None, ""
    args = candidate_args(statement)
    if args is None:
        return False, "row theorem is not a cpsTripleWithin conclusion", None, ""
    cr = resolver.expand(args[4], theorem_path)
    pair = of_prog(cr)
    if pair is None:
        return False, "cr does not resolve to CodeReq.ofProg", None, ""
    base, prog_token = pair
    anchored = anchored_symbol(base)
    if anchored != row.symbol:
        return False, f"CodeReq anchor is {anchored or 'unresolved'}", None, ""
    prog_name = strip_outer(prog_token).rsplit(".", 1)[-1]
    candidates = [d for d in decls if d.name == prog_name]
    if len(candidates) != 1:
        return False, f"Program {prog_name} resolves to {len(candidates)} declarations", None, ""
    program = candidates[0]
    instructions, parse_warnings = parse_program(program)
    calls, call_warnings = parse_calls(instructions)
    if parse_warnings:
        if (all("no instruction lines parsed" in warning
                for warning in parse_warnings) and
                not re.search(r"\.([A-Z][A-Z0-9_]*)\b", program.body)):
            return False, "not-candidate: Program alias/combinator is outside the direct parser", None, prog_name
        return False, "; ".join(parse_warnings), None, prog_name
    if call_warnings:
        return False, "; ".join(call_warnings), None, prog_name
    raw_external = [call for call in calls if call.target != row.symbol]
    if not raw_external:
        return False, "not-candidate: no direct external JAL in Program", None, prog_name
    external, target_problems = partition_external_targets(
        anchored, len(instructions), raw_external, addresses)
    if target_problems:
        return False, "; ".join(target_problems), None, prog_name
    if not external:
        return False, "not-candidate: all direct calls remain inside the Program image", None, prog_name
    branches, jumps, transfer_warnings = parse_branches(instructions, row.symbol)
    if transfer_warnings:
        return False, "; ".join(transfer_warnings), None, prog_name
    pre = resolver.expand(args[5], theorem_path)
    residual = has_residual_hypothesis(statement, resolver, theorem_path)
    analysis = analyze(instructions, external, branches, jumps, pre, row.symbol,
                       statement, residual)
    return True, "", analysis, prog_name


def scan() -> tuple[list[Row], list[tuple[Row, Analysis, str]], list[str]]:
    routines_text = ROUTINES.read_text(errors="replace")
    all_decls, texts = all_sources()
    resolver = Resolver(all_decls)
    addresses = guest_address_values()
    structural: list[tuple[Row, Analysis, str]] = []
    problems: list[str] = []
    for row in rows(routines_text):
        if row.tier != "conditional" or not row.ref:
            continue
        theorem = find_theorem(row.ref, texts)
        if theorem is None:
            continue
        path, text = theorem
        ok, reason, analysis, prog_name = inspect_row(
            row, path, text, resolver, all_decls, addresses)
        if ok and analysis is not None:
            structural.append((row, analysis, prog_name))
        elif (reason in {
            "theorem declaration not found",
            "row theorem is not a cpsTripleWithin conclusion",
            "cr does not resolve to CodeReq.ofProg",
        } or reason.startswith("CodeReq anchor is ") or
              reason.startswith("not-candidate:")):
            continue
        else:
            # Once a row has the right CodeReq spine and a Program-shaped
            # candidate, an unparsed call/branch/address is not absence of a
            # match: it is an instrument limitation.  Fail closed so a new
            # syntax cannot silently lower this detector's bound.
            problems.append(f"{row.symbol}: {reason}")
    return rows(routines_text), structural, problems


def current_git_head() -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, check=True,
            capture_output=True, text=True)
        return result.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def is_inline_arm(row: Row) -> bool:
    """Recognize an arm-qualified theorem rather than a whole-wrapper top."""
    return bool(row.ref) and not row.ref.startswith(row.symbol + "_spec")


def outcome_label(row: Row, analysis: Analysis) -> str:
    """Separate confirmed hits, exclusions, and fail-closed uncertainty."""
    if analysis.status == "unknown":
        return "unknown-failed-closed"
    if analysis.residual:
        if analysis.status == "reachable":
            return "confirmed wrapper-plus-residual"
        return "excluded domain-gated wrapper-plus-residual"
    if is_inline_arm(row):
        return "excluded inline-arm direct-call control"
    if analysis.status == "gated-away":
        return "excluded domain-gated direct-call control"
    return "excluded no-residual direct-call control"


def report(rows_seen: list[Row], matches: list[tuple[Row, Analysis, str]]) -> list[str]:
    problems: list[str] = []
    by_symbol = {row.symbol: (row, analysis, prog) for row, analysis, prog in matches}
    print(f"wrapper-JAL direct-call candidates at {current_git_head()}: "
          f"{len(matches)} (lower bound; direct JAL only)")
    for row, analysis, prog in sorted(matches, key=lambda x: x[0].symbol):
        targets = ", ".join(sorted({call.target for call in analysis.calls}))
        print(f"  {row.symbol}: {outcome_label(row, analysis)}; "
              f"Program={prog} external={targets}")
        for note in analysis.evidence[:3]:
            print(f"    evidence: {note}")
    residual_matches = [row.symbol for row, analysis, _ in matches
                        if analysis.residual]
    no_residual = [row.symbol for row, analysis, _ in matches
                   if not analysis.residual]
    inline_arms = [row.symbol for row, analysis, _ in matches
                   if outcome_label(row, analysis) ==
                   "excluded inline-arm direct-call control"]
    confirmed = [row.symbol for row, analysis, _ in matches
                 if outcome_label(row, analysis).startswith("confirmed ")]
    unknown = [row.symbol for row, analysis, _ in matches
               if analysis.status == "unknown"]
    print("third-stage residual classification:")
    print("  wrapper-plus-residual candidates: "
          + (", ".join(sorted(residual_matches)) or "none"))
    print("  direct-call controls excluded from the vacuity signature: "
          + (", ".join(sorted(no_residual)) or "none"))
    print("  arm-qualified inline controls (mechanically excluded): "
          + (", ".join(sorted(inline_arms)) or "none"))
    print("outcome counts: "
          f"confirmed={len(confirmed)}, "
          f"excluded={len(matches) - len(confirmed) - len(unknown)}, "
          f"unknown-failed-closed={len(unknown)}")
    print(f"historical four-row census was measured at {HISTORICAL_CENSUS_SHA}; "
          "the current candidate population is reported with its own tree SHA")
    print("stage-two domain analysis: actual registered precondition + parsed CFG;")
    print("  unknown control-flow/alias shapes are findings, not inferred safety")
    print("method lower bound: indirect JALR, dispatch tables, generated/runtime strings,")
    print("  and unresolved Program aliases/unions are outside this detector")

    for symbol, expected in EXPECTED.items():
        item = by_symbol.get(symbol)
        if item is None:
            problems.append(f"regression fixture missing structural match: {symbol}")
            continue
        row, analysis, _prog = item
        if row.ref != EXPECTED_REFS[symbol]:
            problems.append(f"{symbol}: proof reference changed to {row.ref!r}; re-audit fixture")
        if analysis.status != expected:
            problems.append(f"{symbol}: expected stage-two {expected}, got {analysis.status}")

    for symbol, (row, analysis, _prog) in by_symbol.items():
        if analysis.status == "unknown":
            problems.append(f"{symbol}: unknown-failed-closed; review unsupported "
                            "control-flow or domain syntax")
        elif symbol not in EXPECTED and analysis.residual:
            problems.append(f"new wrapper-plus-residual match requires review: "
                            f"{symbol} ({analysis.status})")
        elif symbol in EXPECTED and analysis.status == "unknown":
            problems.append(f"{symbol}: stage-two reachability is unknown")

    if len(matches) < len(EXPECTED):
        problems.append("structural census fell below the four-row regression floor")
    return problems


def synthetic_scan() -> tuple[list[tuple[str, str]], list[str]]:
    """Small end-to-end controls for both stages, kept independent of the tree."""
    def run(name: str, program: str, pre: str) -> tuple[str, str]:
        path = ROOT / "<self-test>"
        decl = Decl(name + "_prog", path, 1, program)
        instructions, warnings = parse_program(decl)
        calls, warnings2 = parse_calls(instructions)
        branches, jumps, warnings3 = parse_branches(instructions, name)
        if warnings + warnings2 + warnings3:
            return name, "unknown"
        external = [c for c in calls if c.target != name]
        return name, analyze(instructions, external, branches, jumps, pre, name).status

    controls = [
        ("synthetic_live",
         "[ .JAL .x1 (jalOff GuestAddrs.synthetic_callee (GuestAddrs.synthetic_live + 0)),\n"
         "  .JALR .x0 .x1 (0 : BitVec 12) ]",
         "(.x0 ↦ᵣ (0 : Word))"),
        ("synthetic_gated",
         "[ .BEQ .x5 .x0 (brOff (GuestAddrs.synthetic_gated + 8) (GuestAddrs.synthetic_gated + 0)),\n"
         "  .JAL .x1 (jalOff GuestAddrs.synthetic_callee (GuestAddrs.synthetic_gated + 4)),\n"
         "  .JALR .x0 .x1 (0 : BitVec 12) ]",
         "(.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word))"),
        ("synthetic_unknown",
         "[ .BEQ .x5 .x6 (brOff (GuestAddrs.synthetic_unknown + 8) (GuestAddrs.synthetic_unknown + 0)),\n"
         "  .JAL .x1 (jalOff GuestAddrs.synthetic_callee (GuestAddrs.synthetic_unknown + 4)),\n"
         "  .JALR .x0 .x1 (0 : BitVec 12) ]",
         "(.x0 ↦ᵣ (0 : Word))"),
    ]
    results: list[tuple[str, str]] = [run(*control) for control in controls]
    failures = []
    expected = {"synthetic_live": "reachable", "synthetic_gated": "gated-away",
                "synthetic_unknown": "reachable"}
    # The unknown control has an unconstrained branch, so an existential path
    # to the call is genuinely reachable; this guards against treating an
    # unforced branch as an early-exit proof.
    for name, got in results:
        if got != expected[name]:
            failures.append(f"{name}: expected {expected[name]}, got {got}")
    return results, failures


def self_test() -> int:
    results, failures = synthetic_scan()
    if failures:
        print("SELF-TEST: FAIL")
        for failure in failures:
            print("  " + failure)
        return 1
    # A planted path-control corruption must be visible in the same run as the
    # clean controls.  Replacing the forced zero with a nonzero fact changes
    # the stage-two result from gated-away to reachable.
    path = ROOT / "<self-test>"
    planted_decl = Decl(
        "synthetic_planted_prog", path, 1,
        "[ .BEQ .x5 .x0 (brOff (GuestAddrs.synthetic_planted + 8) "
        "(GuestAddrs.synthetic_planted + 0)),\n"
        "  .JAL .x1 (jalOff GuestAddrs.synthetic_callee "
        "(GuestAddrs.synthetic_planted + 4)),\n"
        "  .JALR .x0 .x1 (0 : BitVec 12) ]")
    instructions, warnings = parse_program(planted_decl)
    calls, call_warnings = parse_calls(instructions)
    branches, jumps, transfer_warnings = parse_branches(
        instructions, "synthetic_planted")
    planted_warnings = warnings + call_warnings + transfer_warnings
    planted_status = "unknown"
    if not planted_warnings:
        planted_status = analyze(
            instructions, [c for c in calls if c.target != "synthetic_planted"],
            branches, jumps, "(.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (1 : Word))",
            "synthetic_planted").status
    if planted_status != "reachable":
        print("SELF-TEST: FAIL -- planted domain change was not detected; "
              f"got {planted_status}")
        return 1
    outside_call = Call(1, "synthetic_callee", 1)
    outside, target_problems = partition_external_targets(
        "synthetic_live", 3, [outside_call],
        {"synthetic_live": 0x1000, "synthetic_callee": 0x100c})
    if target_problems or len(outside) != 1:
        print("SELF-TEST: FAIL -- target at the image boundary was rejected")
        return 1
    outside, target_problems = partition_external_targets(
        "synthetic_live", 3, [outside_call],
        {"synthetic_live": 0x1000, "synthetic_callee": 0x1008})
    if target_problems or outside:
        print("SELF-TEST: FAIL -- target inside the image was accepted")
        return 1
    unknown_row = Row("synthetic_unknown", "conditional",
                      "synthetic_unknown_spec", "")
    if outcome_label(unknown_row, Analysis("unknown", (), (), ())) != \
            "unknown-failed-closed":
        print("SELF-TEST: FAIL -- unknown outcome was not labelled fail-closed")
        return 1
    print("SELF-TEST: PASS (3 end-to-end CFG controls: reachable, gated-away, "
          "and unconstrained-branch existential reachability; planted "
          "gated-domain change flips to reachable; image-boundary control)")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        rc = self_test()
        if rc:
            return rc
    _rows, matches, scan_problems = scan()
    problems = report(_rows, matches)
    problems.extend(scan_problems)
    if problems:
        print("wrapper-JAL detector: FAIL")
        for problem in problems:
            print("  " + problem)
        return 1
    print("wrapper-JAL detector: PASS (four-row regression fixture classified "
          "2 wrapper-plus-residual reachable / 2 domain-gated; additional "
          "no-residual direct-call controls are reported separately)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
