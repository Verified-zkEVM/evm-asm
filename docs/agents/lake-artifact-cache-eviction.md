# Lake artifact-cache eviction incident

On 2026-08-02, the hourly eviction job for the `yoichi-bkp` account had been
failing before argument parsing for weeks. `default_cache` called
`command -v lake` before reading the explicit `--cache` argument; cron's PATH
does not contain `~/.elan/bin`, so every run logged `cannot locate lake for
default cache dir` and exited.

The cache measured 532.00 GiB (535G via `du -sh`) before repair. After fixing
the default-cache lookup and running the configured eviction, 131,848
cache-only artifacts were removed, reclaiming approximately 488.49 GiB.
24,173 artifacts with `nlink > 1` were deliberately retained because they are
hard-linked into live checkout `.lake/build` trees. The cache measured 44.94 GiB
afterward (48G via `du -sh`, 49,720,669,343 bytes).

The eviction policy is intentionally above the measured live floor:
`--cap-gb 120 --target-gb 80`. A lower cap would fire on every hourly run while
the live hard-linked set is about 45 GiB, turning the guard into constant noise.
The script keeps the `LAKE_CACHE_DIR` override and explicit `--cache` option,
but its fallback is the absolute cache path used by this account, so cron does
not depend on PATH or an interactive Lake installation.

There is one shared `lake-artifact-cache` directory under `/home/yoichi-bkp`;
`evm-asm2`, `evm-asm3`, and `evm-asm-codex2` have separate checkout `.lake`
trees but no separate artifact-cache directories.
