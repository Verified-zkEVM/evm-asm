# Post-merge EEST audit sets

This is the acceptance manifest for the one deferred full audit.  Run it only
after the merged `main` ELF contains #10931; do not reuse a pre-merge sweep or
select fresh work from the frozen queue first.

The sweep must record the resolved guest ELF path and SHA, `main` commit, runner
SHA, manifest denominator, and the instrument SHA.  Classify each named fixture
by its observed verdict/fail code and retain the raw rows used for comparison.

## Expected absent from the false-reject population

- `16190`
- `16226`
- `03489`
- `03492`
- the `23725` residual class
- all 81 `shallow_stack` rows
- `16397`
- `16398`

These are expected to have retired from the residual through merged work.  A
named row still present is a finding, not a reason to regenerate the queue
silently.

## Expected present with a changed result

- `00504`: fail code `60` before #10931; expected fail code `0` after #10931.
- `00337`: retain as the #10876 measured-symptom control.  The source audit
  eliminated the callable-reset explanation but did not retire this measured
  symptom; classify its post-merge result as pass, unchanged failure, or a
  changed failure code.

## Staleness note

The frozen ranked queue predates #10910, #10913, #10906, #10920, #10921,
#10923, #10925, #10928, #10929, #10930, and #10931.  It is therefore not a
source of new work until this audit has reconciled the post-merge head.
