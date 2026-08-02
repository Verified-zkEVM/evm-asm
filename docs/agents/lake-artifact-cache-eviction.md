# Lake artifact-cache eviction incident

On 2026-08-02, the hourly Lake artifact-cache eviction job had been failing
for weeks while appearing to be installed correctly. The crontab entry was
present, the script was executable, and the cache path was valid. The failure
happened before argument parsing because the script tried to locate `lake`
through `PATH` while running under cron; cron did not include the interactive
Lake installation. The only evidence was one line in a log that nobody read,
once an hour, for weeks.

This is the durable lesson: an installed scheduled job needs an observable
health signal, and its failure path must not depend on interactive environment
assumptions. A periodic log line is not monitoring if nobody checks it. The
job's exit status and log should be surfaced to an alert or a regularly
reviewed health check.

The cache reached about 532 GiB before the failure was found. Repairing the
eviction path removed 131,848 cache-only artifacts and reclaimed approximately
488.49 GiB. A further 24,173 artifacts with `nlink > 1` were retained because
they were hard-linked into live checkout `.lake/build` trees. The live floor
was therefore about 45 GiB after cleanup.

The selected eviction policy is `--cap-gb 120 --target-gb 80`, deliberately
above that measured live floor. A cap below the live floor would make every
hourly run report over-cap forever, turning the useful signal into permanent
noise. The sizes will become stale; the existence of a shared live hard-linked
floor, and the reason the cap stays above it, are the lasting tuning guidance.
