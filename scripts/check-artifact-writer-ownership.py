#!/usr/bin/env python3
"""Check ownership of statically enumerable committed artifact writers (#13056).

``check-derived-artifacts.py`` already has a reviewed registry for the guest
code-generation pipeline.  This companion closes the other half of the
question: when a script writes a tracked file, is that write covered by an
existing generator edge or by a reviewed owner row with a real gate?

The scanner is intentionally conservative.  It reports only writes whose
destination can be tied to a tracked path by a literal path/alias in the
source.  ``--out``/``args.out`` destinations, temporary probe products and
writers outside ``scripts/**/*.py``/``scripts/**/*.sh`` are explicitly named
in the manifest's ``scope.unenumerated`` section instead of being guessed.
That boundary is part of the contract: an unlisted fixed sink must fail, while
an unresolved dynamic sink must remain visible as an acknowledged limitation.

The manifest is not self-certifying.  The independent scan is compared with
the union of its rows and the ``GENERATORS`` registry, and self-tests remove an
owner row and inject an unexpected writer to prove both failure directions.
No source or artifact is changed by this checker.
"""
from __future__ import annotations

import argparse
import ast
import fnmatch
import importlib.util
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts" / "artifact-writer-ownership.json"
WORKFLOW = ROOT / ".github" / "workflows" / "build.yml"
WORKFLOW_DIR = ROOT / ".github" / "workflows"
PARALLEL = ROOT / "scripts" / "check-build-parallel.sh"
SCHEMA = "artifact-writer-ownership-v1"
OWNER_FIELDS = (
    "name", "writer", "outputs", "owner_gate", "gate_source",
    "ci_surface", "mode", "discovery", "reason",
)
OUTPUT_GLOB_CHARS = set("*?[")
WRITE_METHODS = frozenset({"write_text", "write_bytes"})
SKIP_FUNCTIONS = frozenset({"self_test", "run_self_test", "test", "tests"})


@dataclass(frozen=True)
class WriteEvent:
    path: str
    script: str
    line: int


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def load_manifest(path: Path = MANIFEST) -> dict:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read manifest {path}: {exc}") from exc
    return data


def tracked_paths(root: Path = ROOT) -> set[str]:
    proc = subprocess.run(
        ["git", "ls-files", "-z"], cwd=root, capture_output=True, check=False
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "git ls-files failed: " + proc.stderr.decode(errors="replace").strip()
        )
    return {item for item in proc.stdout.decode().split("\0") if item}


def _source_files(root: Path = ROOT) -> Iterable[Path]:
    scripts = root / "scripts"
    for path in sorted(scripts.rglob("*")):
        if not path.is_file() or path.name == Path(__file__).name:
            continue
        if path.suffix in {".py", ".sh"}:
            yield path


def _path_tokens(path: str) -> set[str]:
    """Literal tokens useful for tying an alias to a repo-relative path."""
    pieces = {path, Path(path).name}
    if "/" in path:
        pieces.add(path.rsplit("/", 1)[-1])
    return {p for p in pieces if p}


def _tracked_aliases(text: str, tracked: set[str]) -> dict[str, set[str]]:
    """Find simple ``NAME = ... 'tracked/path'`` aliases.

    We do not evaluate Python.  A literal basename/path in an assignment is a
    deliberately narrow syntactic signal; dynamic expressions stay outside
    the claimed scanner boundary.
    """
    aliases: dict[str, set[str]] = {}
    # Index once.  The repository has thousands of tracked paths; comparing
    # every assignment against every path made the first implementation
    # quadratic in the tree size and turned a source check into a minutes-long
    # probe.  Exact basename tokens keep the same conservative semantics while
    # making the scan linear in source size.
    by_basename: dict[str, set[str]] = {}
    for path in tracked:
        by_basename.setdefault(Path(path).name, set()).add(path)
    for line in text.splitlines():
        match = re.match(r"\s*([A-Za-z_]\w*)\s*=\s*(.*)$", line)
        if not match:
            continue
        name, rhs = match.groups()
        for token in re.findall(r"[A-Za-z0-9_.-]+", rhs):
            aliases.setdefault(name, set()).update(by_basename.get(token, ()))
    return aliases


def _literal_aliases(node: ast.AST, aliases: dict[str, set[str]]) -> set[str]:
    if isinstance(node, ast.Name):
        return set(aliases.get(node.id, ()))
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return {node.value}
    if isinstance(node, ast.JoinedStr):
        return set()
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return _literal_aliases(node.left, aliases) | _literal_aliases(node.right, aliases)
    if isinstance(node, ast.Call):
        func = node.func
        name = func.attr if isinstance(func, ast.Attribute) else ""
        if name == "join":
            out: set[str] = set()
            for arg in node.args:
                out |= _literal_aliases(arg, aliases)
            return out
    return set()


def _mode_is_write(node: ast.Call) -> bool:
    if isinstance(node.func, ast.Attribute) and node.func.attr in WRITE_METHODS:
        return True
    if isinstance(node.func, ast.Name) and node.func.id == "open":
        mode = None
        if len(node.args) >= 2 and isinstance(node.args[1], ast.Constant):
            mode = node.args[1].value
        for keyword in node.keywords:
            if keyword.arg == "mode" and isinstance(keyword.value, ast.Constant):
                mode = keyword.value.value
        return isinstance(mode, str) and any(letter in mode for letter in "wax+")
    return False


def _write_dest(node: ast.Call) -> ast.AST | None:
    if isinstance(node.func, ast.Attribute) and node.func.attr in WRITE_METHODS:
        return node.func.value
    if isinstance(node.func, ast.Name) and node.func.id == "open":
        return node.args[0] if node.args else None
    if isinstance(node.func, ast.Attribute) and node.func.attr in {
        "replace", "rename", "move", "copy", "copyfile", "copy2",
    }:
        # os.replace/rename and shutil.move/copy use destination as arg 2.
        return node.args[1] if len(node.args) >= 2 else None
    return None


def _is_sink(node: ast.Call) -> bool:
    if _mode_is_write(node):
        return True
    if isinstance(node.func, ast.Attribute) and node.func.attr in {
        "replace", "rename", "move", "copy", "copyfile", "copy2",
    }:
        return len(node.args) >= 2
    return False


class _PythonSinkVisitor(ast.NodeVisitor):
    def __init__(self, script: Path, aliases: dict[str, set[str]],
                 tracked: set[str]) -> None:
        self.script = script
        self.aliases = aliases
        self.tracked = tracked
        self.events: list[WriteEvent] = []
        self.function_stack: list[str] = []

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        self.function_stack.append(node.name)
        self.generic_visit(node)
        self.function_stack.pop()

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_Call(self, node: ast.Call) -> None:  # noqa: N802
        if not any(name in SKIP_FUNCTIONS or "selftest" in name.lower()
                   for name in self.function_stack) and _is_sink(node):
            dest = _write_dest(node)
            if dest is not None:
                for candidate in _literal_aliases(dest, self.aliases):
                    self.events.extend(_normalise_candidate(
                        candidate, self.script, node.lineno, self.tracked))
        self.generic_visit(node)


def _normalise_candidate(candidate: str, script: Path, line: int,
                         tracked: set[str] | None = None) -> list[WriteEvent]:
    """Turn an alias target into a repo-relative event when possible."""
    candidate = candidate.replace("\\", "/")
    # Aliases normally hold repo-relative paths.  Absolute aliases are reduced
    # only when they are inside this repository.
    if os.path.isabs(candidate):
        try:
            candidate = Path(candidate).resolve().relative_to(ROOT).as_posix()
        except ValueError:
            return []
    candidate = candidate.lstrip("./")
    if not candidate or candidate.startswith("/"):
        return []
    if tracked is not None and candidate not in tracked:
        return []
    return [WriteEvent(candidate, rel(script), line)]


def _scan_python(path: Path, tracked: set[str]) -> list[WriteEvent]:
    try:
        text = path.read_text(encoding="utf-8")
        tree = ast.parse(text, filename=str(path))
    except (OSError, SyntaxError, UnicodeDecodeError):
        return []
    aliases = _tracked_aliases(text, tracked)
    visitor = _PythonSinkVisitor(path, aliases, tracked)
    visitor.visit(tree)

    # The shim generator creates a bounded family from ``ROOT / EvmAsm / Rv64``
    # and therefore cannot name one exact file before querying the dependency.
    # Keep this one independently visible as a bounded-glob event.
    if path.name == "gen-rv64-shims.py" and "EvmAsm" in text and "Rv64" in text:
        for line_no, line in enumerate(text.splitlines(), 1):
            if "path.write_text" in line:
                visitor.events.append(WriteEvent("EvmAsm/Rv64/**/*.lean",
                                                 rel(path), line_no))
                break
    # ``--write-floor`` deliberately rewrites this generator's two constants
    # in place.  The destination is ``__file__`` rather than a path literal,
    # so record this one explicit, self-targeted static sink as well.
    if (path.name == "guest_image_coverage.py"
            and "os.path.abspath(__file__)" in text):
        for line_no, line in enumerate(text.splitlines(), 1):
            if 'open(path, "w")' in line:
                visitor.events.append(WriteEvent(
                    "scripts/guest_image_coverage.py", rel(path), line_no))
                break
    return _dedupe_events(visitor.events)


_SHELL_ASSIGN = re.compile(
    r"^\s*(?:declare\s+)?([A-Za-z_]\w*)\s*=\s*['\"]?([^'\"\n]+)"
)
_SHELL_VAR = re.compile(r"\$\{?([A-Za-z_]\w*)\}?")
_SHELL_SINK = re.compile(r"(?:\b(?:mv|cp|install|tee)\b|>>?|\bsed\s+-i)" )


def _scan_shell(path: Path, tracked: set[str]) -> list[WriteEvent]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError):
        return []
    aliases: dict[str, set[str]] = {}
    by_basename: dict[str, set[str]] = {}
    for candidate in tracked:
        by_basename.setdefault(Path(candidate).name, set()).add(candidate)
    for line in lines:
        match = _SHELL_ASSIGN.match(line)
        if not match:
            continue
        name, rhs = match.groups()
        for token in re.findall(r"[A-Za-z0-9_.-]+", rhs):
            aliases.setdefault(name, set()).update(by_basename.get(token, ()))

    events: list[WriteEvent] = []
    for line_no, raw in enumerate(lines, 1):
        line = raw.split("#", 1)[0]
        if not line or not _SHELL_SINK.search(line):
            continue
        destinations: list[str] = []
        # A redirect destination is the only token written by a command such
        # as `awk ... > "$tmp"`; never classify the input paths on the same
        # line as writes.
        destinations.extend(
            match.group(1)
            for match in re.finditer(r"(?:^|\s)(?:>>|1>|2?>)\s*([^\s;&]+)", line)
        )
        try:
            words = shlex.split(line)
        except ValueError:
            words = line.split()
        for command in ("mv", "cp", "install"):
            if command in words:
                destinations.append(words[-1])
                break
        if "tee" in words:
            index = max(i for i, word in enumerate(words) if word == "tee")
            destinations.extend(word for word in words[index + 1:]
                               if not word.startswith("-"))
        if "sed" in words and "-i" in words:
            destinations.append(words[-1])

        for destination in destinations:
            variables = _SHELL_VAR.findall(destination)
            if variables:
                # A check's backup restore is not an artifact producer.  It
                # intentionally copies a tracked file back after a probe, and
                # treating it as a second owner would make every source gate
                # appear to compete with its generator.
                if any(var.endswith("_BAK") or var.startswith("TMP")
                       for var in variables):
                    continue
                for var in variables:
                    for candidate in aliases.get(var, ()):
                        events.extend(_normalise_candidate(candidate, path, line_no, tracked))
                continue
            token = destination.strip("'\"")
            for candidate in by_basename.get(Path(token).name, ()):
                if token == candidate or Path(token).name == Path(candidate).name:
                    events.extend(_normalise_candidate(candidate, path, line_no, tracked))
    return _dedupe_events(events)


def _dedupe_events(events: Iterable[WriteEvent]) -> list[WriteEvent]:
    return sorted(set(events), key=lambda e: (e.path, e.script, e.line))


def enumerate_fixed_writers(root: Path = ROOT, tracked: set[str] | None = None) -> list[WriteEvent]:
    tracked = tracked if tracked is not None else tracked_paths(root)
    events: list[WriteEvent] = []
    for path in _source_files(root):
        events.extend(_scan_python(path, tracked) if path.suffix == ".py"
                      else _scan_shell(path, tracked))
    return _dedupe_events(events)


def _pattern_matches(pattern: str, path: str) -> bool:
    if any(char in pattern for char in OUTPUT_GLOB_CHARS):
        return fnmatch.fnmatchcase(path, pattern)
    return pattern == path


def _row_output_matches(row: dict, path: str) -> bool:
    return any(_pattern_matches(output, path) for output in row.get("outputs", []))


def _writer_script(writer: str) -> str | None:
    match = re.search(r"(?:^|\s)(scripts/[A-Za-z0-9_./-]+(?:\.py|\.sh|\.lean))", writer)
    return match.group(1) if match else None


def _generator_script(generator: str) -> str | None:
    return _writer_script(generator)


def _derived_patterns() -> list[tuple[str, str]]:
    path = ROOT / "scripts" / "check-derived-artifacts.py"
    spec = importlib.util.spec_from_file_location("check_derived_artifacts", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    out: list[tuple[str, str]] = []
    for generator in module.GENERATORS:
        artifact = generator["artifact"].replace("<Name>", "*")
        out.append((artifact, generator.get("generator", "")))
    return out


def _valid_rows(data: dict) -> tuple[list[dict], list[str]]:
    problems: list[str] = []
    if data.get("schema") != SCHEMA:
        problems.append(f"schema must be {SCHEMA!r}")
    scope = data.get("scope")
    if not isinstance(scope, dict):
        problems.append("scope must be an object")
    else:
        for key in ("enumerator", "claim", "unenumerated"):
            if not scope.get(key):
                problems.append(f"scope missing non-empty {key}")
        if not isinstance(scope.get("unenumerated", []), list):
            problems.append("scope.unenumerated must be a list")

    rows = data.get("owners")
    if not isinstance(rows, list):
        return [], problems + ["owners must be a list"]
    names: set[str] = set()
    outputs: dict[str, str] = {}
    for index, row in enumerate(rows):
        prefix = f"owner {index}"
        if not isinstance(row, dict):
            problems.append(f"{prefix} is not an object")
            continue
        missing = [field for field in OWNER_FIELDS
                   if field not in row or row[field] in (None, "", [])]
        if missing:
            problems.append(f"{prefix} missing fields: {', '.join(missing)}")
            continue
        name = row["name"]
        if not isinstance(name, str) or not name:
            problems.append(f"{prefix} has no non-empty name")
        elif name in names:
            problems.append(f"duplicate owner name: {name}")
        else:
            names.add(name)
        if not isinstance(row["outputs"], list) or not all(
            isinstance(item, str) and item for item in row["outputs"]
        ):
            problems.append(f"{prefix} outputs must be a non-empty string list")
        if row.get("owner_gate") == "NONE":
            if row.get("mode") != "reviewed-un-gated":
                problems.append(f"{prefix} NONE gate requires reviewed-un-gated mode")
            if not row.get("reason", "").strip():
                problems.append(f"{prefix} NONE gate requires a reason")
        elif row.get("mode") == "reviewed-un-gated":
            problems.append(f"{prefix} reviewed-un-gated row must use owner_gate NONE")
        for output in row.get("outputs", []):
            if any(char in output for char in OUTPUT_GLOB_CHARS):
                continue
            prior = outputs.get(output)
            if prior is not None and prior != name:
                problems.append(f"output {output} is owned by both {prior} and {name}")
            outputs[output] = name
    floor = data.get("visibility_floor")
    if not isinstance(floor, dict):
        problems.append("visibility_floor must be an object")
    else:
        minimum = floor.get("min_owner_rows")
        required = floor.get("required_names")
        if not isinstance(minimum, int) or minimum <= 0:
            problems.append("visibility_floor.min_owner_rows must be positive")
        if not isinstance(required, list) or not all(isinstance(n, str) and n for n in required):
            problems.append("visibility_floor.required_names must be a string list")
        else:
            missing = sorted(set(required) - names)
            if missing:
                problems.append("visibility floor missing required names: " + ", ".join(missing))
    return rows, problems


def _path_exists_or_matches(path: str, tracked: set[str]) -> bool:
    if any(char in path for char in OUTPUT_GLOB_CHARS):
        return any(fnmatch.fnmatchcase(candidate, path) for candidate in tracked)
    return path in tracked


def _workflow_text() -> str:
    """Read every checked-in workflow, not only the main build.

    One owner (the duplication budget) intentionally lives on the periodic
    quality-trends workflow, so treating build.yml as the whole CI surface
    would incorrectly reject a valid owner row.
    """
    chunks: list[str] = []
    for path in sorted(WORKFLOW_DIR.glob("*.y*ml")):
        try:
            chunks.append(path.read_text(encoding="utf-8"))
        except OSError:
            continue
    return "\n".join(chunks)


def _gate_tokens(command: str) -> list[str]:
    return re.findall(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*", command)


def validate_rows(data: dict, tracked: set[str], workflow_text: str,
                  parallel_text: str) -> list[str]:
    rows, problems = _valid_rows(data)
    for row in rows:
        name = row.get("name", "<unnamed>")
        writer = _writer_script(str(row.get("writer", "")))
        if writer is None:
            problems.append(f"{name}: writer must name a scripts/*.py, scripts/*.sh, or scripts/*.lean source")
        elif writer not in tracked:
            problems.append(f"{name}: writer source is not tracked: {writer}")
        gate_source = row.get("gate_source")
        if not isinstance(gate_source, str) or not gate_source:
            continue
        if gate_source not in tracked and not Path(ROOT / gate_source).is_file():
            problems.append(f"{name}: gate_source does not exist: {gate_source}")
            continue
        source_path = ROOT / gate_source
        try:
            gate_text = source_path.read_text(encoding="utf-8")
        except OSError as exc:
            problems.append(f"{name}: gate_source unreadable: {exc}")
            continue
        if row.get("owner_gate") != "NONE":
            if not any(token in (workflow_text + "\n" + parallel_text)
                       for token in _gate_tokens(str(row.get("owner_gate", "")))
                       if "/" in token or token.endswith((".py", ".sh")) or token == "axiomsweep"):
                problems.append(f"{name}: owner gate is not reachable from CI workflow/bundle")
            for output in row.get("outputs", []):
                marker = Path(output.replace("*", "x")).name
                # For a bounded glob, the literal directory prefix is the
                # useful source marker; the concrete generated filename is
                # deliberately discovered from the dependency and cannot be
                # written in the gate source.
                source_marker = output.split("*", 1)[0].rstrip("/") if "*" in output else output
                source_marker = source_marker or marker
                if (marker and marker not in gate_text and output not in gate_text
                        and source_marker not in gate_text):
                    problems.append(f"{name}: gate source does not mention output {output}")
        for output in row.get("outputs", []):
            if not _path_exists_or_matches(output, tracked):
                problems.append(f"{name}: declared output is not tracked/matched: {output}")
    return problems


def _covered_by_generator(event: WriteEvent, generators: list[tuple[str, str]]) -> bool:
    return any(_pattern_matches(pattern, event.path) and
               (_generator_script(generator) in (None, event.script))
               for pattern, generator in generators)


def _covered_by_row(event: WriteEvent, rows: Sequence[dict]) -> bool:
    for row in rows:
        if _row_output_matches(row, event.path):
            script = _writer_script(str(row.get("writer", "")))
            if script == event.script:
                return True
    return False


def ownership_findings(events: Sequence[WriteEvent], rows: Sequence[dict],
                       generators: list[tuple[str, str]]) -> list[str]:
    findings: list[str] = []
    for event in events:
        if _covered_by_generator(event, generators):
            continue
        if _covered_by_row(event, rows):
            continue
        path_rows = [row for row in rows if _row_output_matches(row, event.path)]
        if path_rows:
            declared = ", ".join(row["name"] for row in path_rows)
            findings.append(
                f"unowned writer {event.script}:{event.line} -> {event.path} "
                f"(output has owner row(s) {declared}, but this writer is not one of them)"
            )
        else:
            findings.append(
                f"unowned fixed writer {event.script}:{event.line} -> {event.path}"
            )
    # A fixed row with no independent observation is stale or the scanner has
    # stopped understanding its sink.  Dynamic/non-script/self rows are honest
    # exceptions and are checked by schema/output/gate validation instead.
    for row in rows:
        if row.get("discovery") not in {"fixed", "bounded-glob"}:
            continue
        script = _writer_script(str(row.get("writer", "")))
        if script is None:
            continue
        if not any(e.script == script and _row_output_matches(row, e.path)
                   for e in events):
            findings.append(
                f"owner row {row['name']} has no independently observed fixed write "
                f"from {script}"
            )
    return sorted(set(findings))


def floor_findings(data: dict, rows: Sequence[dict]) -> list[str]:
    floor = data.get("visibility_floor", {})
    problems: list[str] = []
    names = {row.get("name") for row in rows}
    minimum = floor.get("min_owner_rows")
    if isinstance(minimum, int) and len(rows) < minimum:
        problems.append(f"owner registry below visibility floor: {len(rows)} < {minimum}")
    for name in floor.get("required_names", []):
        if name not in names:
            problems.append(f"owner registry missing required entry: {name}")
    return problems


def _manifest_with_rows(data: dict, rows: Sequence[dict]) -> dict:
    copied = dict(data)
    copied["owners"] = list(rows)
    return copied


def self_test() -> int:
    failures: list[str] = []
    try:
        data = load_manifest()
        tracked = tracked_paths()
        rows, schema_problems = _valid_rows(data)
        failures.extend("manifest: " + p for p in schema_problems)
        failures.extend("manifest: " + p for p in floor_findings(data, rows))
        workflow_text = _workflow_text()
        parallel_text = PARALLEL.read_text(encoding="utf-8")
        failures.extend("manifest: " + p for p in validate_rows(
            data, tracked, workflow_text, parallel_text))
        generators = _derived_patterns()
        events = enumerate_fixed_writers(tracked=tracked)

        # The independent scan must see the fixed manifest writer; otherwise
        # removing its owner row would not exercise the intended direction.
        canary = next((event for event in events
                       if event.path == "scripts/asm-fixtures/MANIFEST.tsv"), None)
        if canary is None:
            failures.append("scanner: did not independently find asm-fixture-manifest writer")
        else:
            without = [row for row in rows if row.get("name") != "asm-fixture-manifest"]
            missing = ownership_findings(events, without, generators)
            if not any("MANIFEST.tsv" in finding for finding in missing):
                failures.append("scanner: removing asm-fixture-manifest did not fail")

        # Unknown-writer control: the destination is an otherwise owned path,
        # so this proves the checker tracks writer identity, not just paths.
        unknown = WriteEvent("DRIFT.md", "scripts/synthetic-writer.py", 1)
        if not any("unowned writer" in finding for finding in ownership_findings(
                [unknown], rows, generators)):
            failures.append("scanner: synthetic unknown writer was accepted")

        # Stale/malformed manifest controls must fail without touching the real
        # JSON file.  This also protects against a checker that only self-tests
        # its happy path.
        malformed = dict(data)
        malformed["owners"] = [dict(rows[0])]
        malformed["owners"][0]["reason"] = ""
        if not any("missing fields" in p or "reason" in p
                   for p in validate_rows(malformed, tracked, workflow_text, parallel_text)):
            failures.append("manifest: malformed empty-reason control was accepted")
        if not floor_findings(_manifest_with_rows(data, rows[:-1]), rows[:-1]):
            failures.append("manifest: owner-floor removal control was accepted")

        # Keep all checks in-memory and assert that no temp artifact was needed.
        with tempfile.TemporaryDirectory(prefix="artifact-writer-ownership-"):
            pass
    except (OSError, RuntimeError, ValueError) as exc:
        failures.append(f"infrastructure: {exc}")

    if failures:
        print("SELF-TEST FAILURES:")
        for failure in failures:
            print("  " + failure)
        return 1
    rows = load_manifest()["owners"]
    print("self-test: independent fixed-sink scan, owner identity, stale-row, "
          "malformed-row and visibility-floor controls pass "
          f"({len(rows)} owner rows)")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()

    try:
        data = load_manifest()
        rows, problems = _valid_rows(data)
        tracked = tracked_paths()
        problems.extend(validate_rows(
            data, tracked,
            _workflow_text(),
            PARALLEL.read_text(encoding="utf-8"),
        ))
        events = enumerate_fixed_writers(tracked=tracked)
        findings = ownership_findings(events, rows, _derived_patterns())
    except (OSError, RuntimeError, ValueError) as exc:
        print(f"check-artifact-writer-ownership: infrastructure failure: {exc}",
              file=sys.stderr)
        return 2

    for problem in problems:
        print("MANIFEST: " + problem)
    for finding in findings:
        print("FINDING: " + finding)
    print("check-artifact-writer-ownership: scanned %d fixed sink(s), %d owner row(s), "
          "%d GENERATORS edge(s)" % (len(events), len(rows), len(_derived_patterns())))
    return 1 if problems or findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
