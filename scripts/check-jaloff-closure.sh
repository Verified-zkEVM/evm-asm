#!/usr/bin/env bash
# jalOff-closure gate (GH #12403 cr-track, holes tracked in #12705): every
# jalOff target of every guestImageEntries program must itself be a first
# component of guestImageEntries — i.e. the registered image is closed under
# direct (JAL) calls. Known holes live in scripts/jaloff-closure-allow.txt
# (rowed-liveness-allow.txt style: symbol, tracking issue, reason). Pure
# source scan, seconds, no build. See scripts/check-jaloff-closure.py for
# the mechanism.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check-jaloff-closure.py "$@"
