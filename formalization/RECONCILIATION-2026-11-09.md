# Branch reconciliation — 9 November 2026

The authoritative numbered register is [TARGETS.json](TARGETS.json):
**170 checked, 2 inherited calculator statements, 17 pending / 189**.
Remaining by paper: 02: 1; 06: 8; 08: 5; 12: 3.

## Why the external agent saw 19

Our six-Codex checkpoint `b9fab9ed` was committed locally and had not been
pushed. It closes the exact printed paper12 `cor:finite` and paper08 `lem:row`,
reducing pending statements from 19 to 17. An external checkout could not see
that local commit. The external agent's `cb19f838` independently continued
from the same parent `9cbe6c5a`; it adds 34 supporting targets without closing
a numbered statement, so its 168/2/19 snapshot was accurate for its branch.
The two counts describe different trees.

## What was combined

Both checkpoint histories are now preserved. The external agent's 51 new
modules and six accepted packets are combined with the six-Codex checkpoint,
its source closures, supporting work and preserved unfinished drafts.
The register retains both sets of supporting component metadata and our
two whole-source adoptions. Both sets of root imports are retained.

GitHub had 17 branch heads at inspection. Most older branch names identify
ancestors already contained in the cumulative continuation. One older branch,
`formalization/leveltwo-counterexamples-2026-11-06`, had a unique commit
`037066d2`: eight exact supporting source-admission/guarded-compilation targets
in five Lean files. That history, evidence and exact gate are also included.
It does not prove the remaining whole level-two decision theorem.

Every local and fetched remote branch head is contained in the reconciled
history. Main can therefore be advanced to this combined checkpoint without
discarding any branch's commits. No old branch was deleted or force-updated.
The branch inventory and validation records are in
[verification/reconciliation-2026-11-09](verification/reconciliation-2026-11-09/).

## Verification and current scope

The 50 external component sources match their successful native rows; all
166 frozen specification/supplier comparisons and 34 exact standard-axiom
closures match. The external aggregate source matches its passed receipt.
All 440 source hashes in the older admission gate's accepted dependency
closure still match, including its five accepted source files and eight
standard-axiom aliases. All 388 current six-Codex source hashes remain
unchanged. Register reconciliation preserves exactly 189 distinct statements.

This reconciliation changes imports, metadata and handoffs. Mathematical
source files and their frozen targets are preserved byte for byte. No new
Lean compilation or full-root/CI pass is claimed; the existing source-matched
native proof evidence is retained and rechecked. The earlier final row
import-only aggregate's memory-admission stop remains recorded as pending.

All six lanes remain stopped, and the local compiler policy remains paused.
The current user request authorizes this finite Git reconciliation onto main;
it does not restart proof research, successors, agents or compiler queues.
Pending tasks and historical continuation instructions do not authorize a
resume. New mathematical work requires explicit user instruction.
