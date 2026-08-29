#!/usr/bin/env python3
"""Evaluate the pirapira open-PR WIP gate.

The workflow owns the GitHub API calls and the close/comment side effects.  This
module performs the queue count and the structural batch classification.  A
batch is established by commit ancestry (or an explicit maintainer label), not
by a branch or title spelling that the PR author controls.  The workflow checks
out trusted repository code and fetches the open PR heads before invoking this
module, while tests inject an ancestry predicate.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections.abc import Callable, Iterable
from typing import Any


DEFAULT_AUTHOR = "pirapira"
DEFAULT_THRESHOLD = 5
BATCH_MIN_COMPONENT_HEADS = 2
# This is a regression floor for the structural classifier itself.  The
# self-test carries two independent positive ancestry fixtures; if a future
# edit silently makes history-based classification return false everywhere,
# the gate fails its own self-test instead of widening the exemption.
STRUCTURAL_BATCH_RECOGNITION_FLOOR = 2
GATE_WORKFLOW_PATH = ".github/workflows/pirapira-wip-gate.yml"


def _value(pr: dict[str, Any], *keys: str, default: Any = None) -> Any:
    """Return the first present key, including GitHub's two API spellings."""

    for key in keys:
        if key in pr:
            return pr[key]
    return default


def pull_number(pr: dict[str, Any]) -> int | None:
    value = _value(pr, "number")
    try:
        return int(value) if value is not None else None
    except (TypeError, ValueError):
        return None


def author_login(pr: dict[str, Any]) -> str:
    author = _value(pr, "author", "user", default={}) or {}
    if isinstance(author, dict):
        return str(author.get("login", ""))
    return ""


def branch_name(pr: dict[str, Any]) -> str:
    head = _value(pr, "head", default={}) or {}
    head_ref = head.get("ref", "") if isinstance(head, dict) else ""
    return str(_value(pr, "headRefName", default=head_ref) or "")


def title(pr: dict[str, Any]) -> str:
    return str(_value(pr, "title", default="") or "")


def labels(pr: dict[str, Any]) -> set[str]:
    raw = _value(pr, "labels", default=[]) or []
    names: set[str] = set()
    for label in raw:
        if isinstance(label, dict):
            name = label.get("name")
        else:
            name = label
        if name is not None:
            names.add(str(name).strip().lower())
    return names


def is_open(pr: dict[str, Any]) -> bool:
    return str(_value(pr, "state", default="open")).lower() == "open"


def _sha(pr: dict[str, Any], side: str) -> str:
    """Read a pull-request head/base SHA from either GitHub API spelling."""

    side_obj = _value(pr, side, default={}) or {}
    nested = side_obj.get("sha", "") if isinstance(side_obj, dict) else ""
    return str(
        _value(pr, f"{side}_sha", f"{side}Sha", f"{side}RefOid", default=nested)
        or ""
    ).strip().lower()


def head_sha(pr: dict[str, Any]) -> str:
    return _sha(pr, "head")


def base_sha(pr: dict[str, Any]) -> str:
    return _sha(pr, "base")


def touches_gate_workflow(pr: dict[str, Any]) -> bool:
    """Whether trusted workflow metadata says this PR edits its own gate."""

    return bool(_value(pr, "touches_gate_workflow", "touchesGateWorkflow", default=False))


def _git_is_ancestor(ancestor: str, descendant: str, *, repo: str = ".") -> bool:
    """Check ancestry, distinguishing a false result from a git failure."""

    result = subprocess.run(
        ["git", "-C", repo, "merge-base", "--is-ancestor", ancestor, descendant],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return True
    if result.returncode == 1:
        return False
    detail = result.stderr.strip() or "git merge-base failed"
    raise RuntimeError(
        f"cannot classify batch ancestry {ancestor[:12]} -> {descendant[:12]}: {detail}"
    )


def structural_batch_head_count(
    pr: dict[str, Any],
    other_open_prs: Iterable[dict[str, Any]],
    *,
    ancestor_checker: Callable[[str, str], bool] | None = None,
    repo: str = ".",
) -> int:
    """Count other open PR heads contained by ``pr`` but not its base.

    A batch is a queue-draining merge of other open PRs.  A branch/title name
    cannot establish that shape; only the candidate's commit graph can.  The
    workflow fetches every open pull ref into the trusted checkout before this
    function is called.  Tests inject ``ancestor_checker`` so the classifier's
    logic stays deterministic and does not need a repository.
    """

    candidate_head = head_sha(pr)
    candidate_base = base_sha(pr)
    if not candidate_head or not candidate_base:
        raise ValueError(
            "structural batch classification requires candidate head.sha and base.sha"
        )
    check_ancestor = ancestor_checker or (
        lambda ancestor, descendant: _git_is_ancestor(
            ancestor, descendant, repo=repo
        )
    )
    count = 0
    candidate_number = pull_number(pr)
    for other in _deduplicate(other_open_prs):
        other_number = pull_number(other)
        other_head = head_sha(other)
        if (candidate_number is not None and other_number == candidate_number) or (
            other_head and other_head == candidate_head
        ):
            continue
        if not other_head or not base_sha(other):
            raise ValueError(
                "structural batch classification requires every open PR to have "
                "head.sha and base.sha"
            )
        # A head already in the candidate's base is not a component being
        # drained by this PR; it is already merged into the queue baseline.
        if check_ancestor(other_head, candidate_base):
            continue
        if check_ancestor(other_head, candidate_head):
            count += 1
    return count


def _batch_classification(
    pr: dict[str, Any],
    other_open_prs: Iterable[dict[str, Any]] | None = None,
    *,
    ancestor_checker: Callable[[str, str], bool] | None = None,
    repo: str = ".",
) -> tuple[bool, int, str]:
    """Return ``(is_batch, structural_count, reason)`` for one PR."""

    if "batch" in labels(pr):
        return True, 0, "maintainer label"
    if other_open_prs is None:
        # There is no graph to inspect, so a naming convention must not grant
        # an exemption.  Callers evaluating a queue pass the peer list.
        return False, 0, "no ancestry evidence"
    count = structural_batch_head_count(
        pr,
        other_open_prs,
        ancestor_checker=ancestor_checker,
        repo=repo,
    )
    return (
        count >= BATCH_MIN_COMPONENT_HEADS,
        count,
        "commit ancestry" if count >= BATCH_MIN_COMPONENT_HEADS else "ordinary PR",
    )


def is_batch(
    pr: dict[str, Any],
    other_open_prs: Iterable[dict[str, Any]] | None = None,
    *,
    ancestor_checker: Callable[[str, str], bool] | None = None,
    repo: str = ".",
) -> bool:
    """Classify a batch by commit ancestry or an explicit maintainer label.

    Branch and title prefixes are intentionally ignored: they are author
    controlled and therefore cannot be an exemption.  A labelled batch remains
    an explicit authority-controlled override.
    """

    return _batch_classification(
        pr,
        other_open_prs,
        ancestor_checker=ancestor_checker,
        repo=repo,
    )[0]


def _flatten_pages(value: Any) -> list[dict[str, Any]]:
    """Flatten ``gh api --paginate --slurp`` output (or a plain array)."""

    if not isinstance(value, list):
        return []
    if not value:
        return []
    if all(isinstance(item, dict) for item in value):
        return [item for item in value if isinstance(item, dict)]
    result: list[dict[str, Any]] = []
    for page in value:
        result.extend(_flatten_pages(page))
    return result


def _deduplicate(prs: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    by_number: dict[int, dict[str, Any]] = {}
    without_number: list[dict[str, Any]] = []
    for pr in prs:
        number = pull_number(pr)
        if number is None:
            without_number.append(pr)
        else:
            by_number[number] = pr
    return list(by_number.values()) + without_number


def evaluate(
    prs: Iterable[dict[str, Any]],
    candidate: dict[str, Any] | None = None,
    *,
    author: str = DEFAULT_AUTHOR,
    threshold: int = DEFAULT_THRESHOLD,
    ancestor_checker: Callable[[str, str], bool] | None = None,
    repo: str = ".",
) -> dict[str, Any]:
    """Return a side-effect-free gate decision and its audit facts."""

    all_prs = list(prs)
    candidate_number = pull_number(candidate) if candidate is not None else None
    if candidate is not None:
        if candidate_number is not None:
            all_prs = [
                pr for pr in all_prs if pull_number(pr) != candidate_number
            ]

    # The candidate is deliberately removed from the count.  The gate measures
    # the existing queue before the new PR is admitted; this means four queued
    # PRs allow the fifth, and six of ten existing PRs landing opens the gate.
    open_prs = [pr for pr in _deduplicate(all_prs) if is_open(pr)]
    author_prs = [pr for pr in open_prs if author_login(pr) == author]

    if ancestor_checker is None:
        ancestry_cache: dict[tuple[str, str], bool] = {}

        def checked_ancestor(ancestor: str, descendant: str) -> bool:
            key = (ancestor, descendant)
            if key not in ancestry_cache:
                ancestry_cache[key] = _git_is_ancestor(
                    ancestor,
                    descendant,
                    repo=repo,
                )
            return ancestry_cache[key]

        effective_ancestor_checker: Callable[[str, str], bool] = checked_ancestor
    else:
        effective_ancestor_checker = ancestor_checker

    classifications: dict[int, tuple[bool, int, str]] = {}

    def classify(pr: dict[str, Any]) -> tuple[bool, int, str]:
        key = pull_number(pr)
        cache_key = key if key is not None else id(pr)
        if cache_key not in classifications:
            classifications[cache_key] = _batch_classification(
                pr,
                open_prs,
                ancestor_checker=effective_ancestor_checker,
                repo=repo,
            )
        return classifications[cache_key]

    batch_prs = [pr for pr in author_prs if classify(pr)[0]]
    counted_prs = [pr for pr in author_prs if not classify(pr)[0]]

    candidate_is_author = candidate is not None and author_login(candidate) == author
    candidate_is_open = candidate is not None and is_open(candidate)
    candidate_batch_count = 0
    candidate_batch_reason = "not evaluated"
    if candidate is not None:
        candidate_is_batch, candidate_batch_count, candidate_batch_reason = _batch_classification(
            candidate,
            open_prs,
            ancestor_checker=effective_ancestor_checker,
            repo=repo,
        )
    else:
        candidate_is_batch = False
    candidate_excluded_from_count = (
        candidate_is_author and candidate_is_open and not candidate_is_batch
    )
    candidate_is_bootstrap = candidate is not None and touches_gate_workflow(candidate)
    should_close = (
        candidate is not None
        and candidate_is_author
        and candidate_is_open
        and not candidate_is_batch
        and not candidate_is_bootstrap
        and len(counted_prs) >= threshold
    )

    if candidate is None:
        reason = "report-only evaluation; no candidate PR was supplied"
    elif not candidate_is_author:
        reason = "candidate author is outside the pirapira gate"
    elif not candidate_is_open:
        reason = "candidate is not open"
    elif candidate_is_batch:
        reason = f"batch PRs are excluded ({candidate_batch_reason})"
    elif candidate_is_bootstrap:
        reason = f"gate workflow changes use the bootstrap exemption ({GATE_WORKFLOW_PATH})"
    elif should_close:
        reason = "open non-batch pirapira count is at or above the threshold"
    else:
        reason = "open non-batch pirapira count is below the threshold"

    return {
        "author": author,
        "threshold": threshold,
        "batch_component_threshold": BATCH_MIN_COMPONENT_HEADS,
        "structural_batch_recognition_floor": STRUCTURAL_BATCH_RECOGNITION_FLOOR,
        "open_count": len(counted_prs),
        "open_pirapira_count_including_batches": len(author_prs),
        "open_batch_count": len(batch_prs),
        "candidate_number": candidate_number,
        "candidate_author": author_login(candidate) if candidate is not None else "",
        "candidate_branch": branch_name(candidate) if candidate is not None else "",
        "candidate_title": title(candidate) if candidate is not None else "",
        "candidate_is_draft": bool(
            _value(candidate, "draft", default=False)
        ) if candidate is not None else False,
        "candidate_structural_batch_head_count": candidate_batch_count,
        "candidate_batch_reason": candidate_batch_reason,
        "candidate_is_batch": candidate_is_batch,
        "candidate_is_bootstrap": candidate_is_bootstrap,
        "candidate_excluded_from_count": candidate_excluded_from_count,
        "should_close": should_close,
        "reason": reason,
    }


def _self_test() -> None:
    """Exercise queue accounting and structural batch classification."""

    def pr(
        number: int,
        *,
        branch: str,
        head: str,
        login: str = DEFAULT_AUTHOR,
        draft: bool = False,
        labels_: list[str] | None = None,
        title_: str | None = None,
        base: str = "base",
        touches_workflow: bool = False,
    ) -> dict[str, Any]:
        return {
            "number": number,
            "state": "open",
            "draft": draft,
            "title": title_ or f"work {number}",
            "head": {"ref": branch, "sha": head},
            "base": {"sha": base},
            "user": {"login": login},
            "labels": labels_ or [],
            "touches_gate_workflow": touches_workflow,
        }

    existing = [
        pr(1, branch="codex/one", head="h1"),
        pr(2, branch="codex/two", head="h2", draft=True),
        pr(3, branch="codex/three", head="h3"),
        pr(4, branch="codex/four", head="h4"),
        pr(5, branch="codex/five", head="h5"),
        pr(6, branch="codex/old", head="h6", labels_=["batch"]),
        pr(7, branch="codex/dhsorens", head="h7", login="dhsorens"),
    ]
    ancestry: set[tuple[str, str]] = set()

    def fake_ancestor(ancestor: str, descendant: str) -> bool:
        return (ancestor, descendant) in ancestry

    candidate = pr(8, branch="codex/new", head="h8")
    result = evaluate(existing, candidate, ancestor_checker=fake_ancestor)
    assert result["open_count"] == 5, result
    assert result["open_batch_count"] == 1, result
    assert result["candidate_excluded_from_count"], result
    assert result["should_close"], result

    # A branch prefix alone cannot exempt a PR any more.
    named_candidate = pr(
        9,
        branch="batch/author-chosen",
        head="h9",
        title_="Batch: author-chosen",
    )
    result = evaluate(existing, named_candidate, ancestor_checker=fake_ancestor)
    assert not result["candidate_is_batch"], result
    assert result["should_close"], result

    # Two other open heads contained in the candidate, but not in its base,
    # establish a batch regardless of its branch/title spelling.
    ancestry.update({("h1", "h10"), ("h2", "h10")})
    batch_candidate = pr(10, branch="codex/wrapper", head="h10")
    result = evaluate(existing, batch_candidate, ancestor_checker=fake_ancestor)
    assert result["open_count"] == 5, result
    assert result["open_batch_count"] == 1, result
    assert result["candidate_is_batch"], result
    assert result["candidate_structural_batch_head_count"] == 2, result
    assert not result["candidate_excluded_from_count"], result
    assert not result["should_close"], result

    # One component is below the threshold; a head already in the base is not
    # a component at all.
    one_component = pr(11, branch="batch/one", head="h11")
    ancestry.add(("h1", "h11"))
    result = evaluate(existing, one_component, ancestor_checker=fake_ancestor)
    assert result["candidate_structural_batch_head_count"] == 1, result
    assert not result["candidate_is_batch"], result
    assert result["should_close"], result

    already_in_base = pr(12, branch="batch/base-plus-one", head="h12")
    ancestry.update({("h1", "base"), ("h2", "h12")})
    result = evaluate(existing, already_in_base, ancestor_checker=fake_ancestor)
    assert result["candidate_structural_batch_head_count"] == 1, result
    assert not result["candidate_is_batch"], result

    # The label remains an authority-controlled override, unlike a title or
    # branch name chosen by the PR author.
    labelled_candidate = pr(13, branch="codex/wrapper", head="h13", labels_=["batch"])
    result = evaluate(existing, labelled_candidate, ancestor_checker=fake_ancestor)
    assert result["candidate_is_batch"], result
    assert result["candidate_batch_reason"] == "maintainer label", result

    # The only non-history exemption is the narrow bootstrap case: a PR that
    # edits this trusted workflow can establish its replacement.
    bootstrap = pr(
        14,
        branch="codex/bootstrap",
        head="h14",
        touches_workflow=True,
    )
    result = evaluate(existing, bootstrap, ancestor_checker=fake_ancestor)
    assert result["candidate_is_bootstrap"], result
    assert not result["should_close"], result

    # Two independent positive fixtures are the recognition floor.  If the
    # ancestry classifier is accidentally reduced to a no-op, this self-test
    # fails instead of silently broadening the WIP exemption.
    ancestry.update({("h1", "h16"), ("h2", "h16"), ("h3", "h15"), ("h4", "h15")})
    first_batch = pr(15, branch="codex/first-wrapper", head="h16", base="base2")
    second_batch = pr(16, branch="codex/second-wrapper", head="h15", base="base2")
    recognized = int(is_batch(first_batch, existing, ancestor_checker=fake_ancestor))
    recognized += int(is_batch(second_batch, existing, ancestor_checker=fake_ancestor))
    assert recognized >= STRUCTURAL_BATCH_RECOGNITION_FLOOR, recognized

    # Missing graph metadata must be loud rather than silently turning a real
    # batch into an ordinary, countable PR.
    incomplete = pr(17, branch="codex/incomplete", head="")
    try:
        evaluate(existing + [incomplete], candidate, ancestor_checker=fake_ancestor)
    except ValueError as exc:
        assert "head.sha" in str(exc), exc
    else:
        raise AssertionError("missing ancestry metadata was accepted")

    already_listed = evaluate(existing, existing[0], ancestor_checker=fake_ancestor)
    assert already_listed["open_count"] == 4, already_listed
    assert already_listed["candidate_excluded_from_count"], already_listed

    print(
        "wip_pr_gate self-test: PASS (queue accounting, structural ancestry, "
        "label/bootstrap overrides; recognition floor "
        f"{STRUCTURAL_BATCH_RECOGNITION_FLOOR})"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prs-file", type=argparse.FileType("r"))
    parser.add_argument("--candidate-file", type=argparse.FileType("r"))
    parser.add_argument("--author", default=DEFAULT_AUTHOR)
    parser.add_argument("--threshold", type=int, default=DEFAULT_THRESHOLD)
    parser.add_argument(
        "--repo",
        default=".",
        help="trusted checkout containing the fetched open-PR heads",
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)

    if args.self_test:
        _self_test()
        return 0
    if args.prs_file is None:
        parser.error("--prs-file is required unless --self-test is used")
    if args.threshold < 1:
        parser.error("--threshold must be positive")

    raw_prs = json.load(args.prs_file)
    prs = _flatten_pages(raw_prs)
    candidate = json.load(args.candidate_file) if args.candidate_file else None
    try:
        result = evaluate(
            prs,
            candidate,
            author=args.author,
            threshold=args.threshold,
            repo=args.repo,
        )
    except (RuntimeError, ValueError) as exc:
        print(f"wip_pr_gate: structural batch classification unavailable: {exc}",
              file=sys.stderr)
        return 2
    json.dump(result, sys.stdout, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
