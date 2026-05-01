#!/usr/bin/env python3
"""Build the weekly benchmark tracking-issue body.

Reads ``history.jsonl`` (current dir) — one JSON object per run, as written
by ``.github/workflows/benchmark.yml`` to the ``benchmark-history`` branch
— and writes ``report.md`` with the latest snapshot plus a Δ table against
the previous run.

Used by ``.github/workflows/benchmark.yml`` (#949 slice 4 / evm-asm-9o8v).

Inputs (env):
- ``GITHUB_REPOSITORY``   — ``owner/repo``, used for hyperlinks.
- ``REGRESSION_PCT``      — soft regression threshold (percent, float).

Output:
- writes ``report.md`` (markdown, suitable for ``gh issue create/edit``).
- exits 0 on success.

The threshold is informational only — the workflow does NOT fail on
regression. See ``docs/benchmark-workflow-design.md`` (c) for rationale.
"""

import json
import os


def fmt_delta(c, p, pct_thr):
    if p is None or p == 0:
        return "n/a", False
    delta = c - p
    pct = 100.0 * delta / p
    sign = "+" if delta >= 0 else ""
    return f"{sign}{delta} ({sign}{pct:.1f}%)", (pct > pct_thr)


def main():
    repo = os.environ["GITHUB_REPOSITORY"]
    pct_thr = float(os.environ["REGRESSION_PCT"])

    with open("history.jsonl") as f:
        lines = [l for l in f if l.strip()]
    cur = json.loads(lines[-1])
    prev = json.loads(lines[-2]) if len(lines) >= 2 else None

    if prev:
        wall_str, wall_regress = fmt_delta(
            cur["wall_seconds"], prev["wall_seconds"], pct_thr
        )
        rss_str, rss_regress = fmt_delta(
            cur["peak_rss_kb"], prev["peak_rss_kb"], pct_thr
        )
    else:
        wall_str, wall_regress = "first run", False
        rss_str, rss_regress = "first run", False
    regress = wall_regress or rss_regress
    badge = "\u26a0\ufe0f regression" if regress else "\u2705 within tolerance"

    commit = cur["commit"]
    commit_short = commit[:12]
    commit_url = f"https://github.com/{repo}/commit/{commit}"
    run_url = f"https://github.com/{repo}/actions/runs/{cur['run_id']}"
    history_url = (
        f"https://github.com/{repo}/blob/benchmark-history/history.jsonl"
    )

    prev_wall_raw = prev["wall_raw"] if prev else "n/a"
    prev_wall_sec = prev["wall_seconds"] if prev else "n/a"
    prev_rss_kb = prev["peak_rss_kb"] if prev else "n/a"

    out = [
        f"## Weekly benchmark report \u2014 {cur['timestamp']}",
        "",
        f"Status: **{badge}** (threshold: +{int(pct_thr)}% on wall or RSS)",
        "",
        "| metric        | current | previous | \u0394 |",
        "|---------------|---------|----------|---|",
        f"| wall (raw)    | `{cur['wall_raw']}` | `{prev_wall_raw}` | \u2014 |",
        f"| wall seconds  | {cur['wall_seconds']} | {prev_wall_sec} | {wall_str} |",
        f"| peak RSS (KB) | {cur['peak_rss_kb']} | {prev_rss_kb} | {rss_str} |",
        "",
        f"- commit: [`{commit_short}`]({commit_url})",
        f"- ref: `{cur['ref']}`",
        f"- trigger: `{cur['trigger']}`",
        f"- runner: `{cur['runner_os']}`, {cur['runner_cores']} cores",
        f"- run: [{cur['run_id']}]({run_url})",
        "",
        f"Full history on the [`benchmark-history`]({history_url}) branch "
        "(one JSON object per run).",
        "",
        "<!-- benchmark-tracking-managed: this issue body is rewritten by "
        ".github/workflows/benchmark.yml on every Monday cron. Comments are "
        "preserved; the body is not. -->",
    ]
    with open("report.md", "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
