#!/usr/bin/env python3
"""Evaluate the pirapira open-PR WIP gate.

The workflow owns the GitHub API calls and the close/comment side effects.  This
module deliberately contains only the metadata classification and count logic,
so the threshold and batch exclusion can be tested without touching GitHub.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Iterable
from typing import Any


DEFAULT_AUTHOR = "pirapira"
DEFAULT_THRESHOLD = 5


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


def is_batch(pr: dict[str, Any]) -> bool:
    """Recognise the repository's established batch-PR naming conventions.

    Batch PRs have historically used ``batch/...`` branches for ordinary
    batches and ``chore/batch-merge-...`` branches for merge-bot batches.  The
    title checks cover already-opened batches whose branch was created by a
    different actor, and the explicit label gives maintainers an escape hatch
    without broad substring matching.
    """

    branch = branch_name(pr).strip().lower()
    pr_title = title(pr).strip().lower()
    return (
        branch.startswith("batch/")
        or branch.startswith("batch-merge/")
        or branch.startswith("chore/batch-merge-")
        or pr_title.startswith("batch:")
        or pr_title.startswith("batch-merge")
        or pr_title.startswith("chore: batch")
        or "batch" in labels(pr)
    )


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
) -> dict[str, Any]:
    """Return a side-effect-free gate decision and its audit facts."""

    all_prs = list(prs)
    if candidate is not None:
        candidate_number = pull_number(candidate)
        if candidate_number is not None:
            all_prs = [
                pr for pr in all_prs if pull_number(pr) != candidate_number
            ]
        all_prs.append(candidate)

    open_prs = [pr for pr in _deduplicate(all_prs) if is_open(pr)]
    author_prs = [pr for pr in open_prs if author_login(pr) == author]
    batch_prs = [pr for pr in author_prs if is_batch(pr)]
    counted_prs = [pr for pr in author_prs if not is_batch(pr)]

    candidate_number = pull_number(candidate) if candidate is not None else None
    candidate_is_author = candidate is not None and author_login(candidate) == author
    candidate_is_open = candidate is not None and is_open(candidate)
    candidate_is_batch = candidate is not None and is_batch(candidate)
    candidate_in_count = (
        candidate_is_author and candidate_is_open and not candidate_is_batch
    )
    should_close = (
        candidate is not None
        and candidate_is_author
        and candidate_is_open
        and not candidate_is_batch
        and len(counted_prs) >= threshold
    )

    if candidate is None:
        reason = "report-only evaluation; no candidate PR was supplied"
    elif not candidate_is_author:
        reason = "candidate author is outside the pirapira gate"
    elif not candidate_is_open:
        reason = "candidate is not open"
    elif candidate_is_batch:
        reason = "batch PRs are excluded from both the count and enforcement"
    elif should_close:
        reason = "open non-batch pirapira count is at or above the threshold"
    else:
        reason = "open non-batch pirapira count is below the threshold"

    return {
        "author": author,
        "threshold": threshold,
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
        "candidate_is_batch": candidate_is_batch,
        "candidate_in_count": candidate_in_count,
        "should_close": should_close,
        "reason": reason,
    }


def _self_test() -> None:
    """Exercise count, candidate inclusion, drafts, and batch exclusion."""

    def pr(number: int, *, branch: str, login: str = DEFAULT_AUTHOR, draft: bool = False) -> dict[str, Any]:
        return {
            "number": number,
            "state": "open",
            "draft": draft,
            "title": f"work {number}",
            "head": {"ref": branch},
            "user": {"login": login},
            "labels": [],
        }

    existing = [
        pr(1, branch="codex/one"),
        pr(2, branch="codex/two", draft=True),
        pr(3, branch="codex/three"),
        pr(4, branch="codex/four"),
        pr(5, branch="batch/old",),
        pr(6, branch="codex/dhsorens", login="dhsorens"),
    ]
    candidate = pr(7, branch="codex/new")
    result = evaluate(existing, candidate)
    assert result["open_count"] == 5, result
    assert result["open_batch_count"] == 1, result
    assert result["candidate_in_count"], result
    assert result["should_close"], result

    batch_candidate = pr(8, branch="chore/batch-merge-1-2",)
    result = evaluate(existing, batch_candidate)
    assert result["open_count"] == 4, result
    assert result["open_batch_count"] == 2, result
    assert result["candidate_is_batch"], result
    assert not result["candidate_in_count"], result
    assert not result["should_close"], result

    already_listed = evaluate(existing, existing[0])
    assert already_listed["open_count"] == 4, already_listed
    assert already_listed["candidate_in_count"], already_listed

    print("wip_pr_gate self-test: PASS (candidate inclusion, drafts, batch exclusion)")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prs-file", type=argparse.FileType("r"))
    parser.add_argument("--candidate-file", type=argparse.FileType("r"))
    parser.add_argument("--author", default=DEFAULT_AUTHOR)
    parser.add_argument("--threshold", type=int, default=DEFAULT_THRESHOLD)
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
    result = evaluate(
        prs,
        candidate,
        author=args.author,
        threshold=args.threshold,
    )
    json.dump(result, sys.stdout, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
