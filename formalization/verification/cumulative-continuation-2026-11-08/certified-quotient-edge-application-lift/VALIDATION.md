# Validation: local original certified quotient-edge application lift

## Exact checks and retained failures

Independent static review accepted all four frozen targets before native
preflight and proof authorship. Comparator-only preflight passed in immutable
receipt `build-reports/1794137275150026527-5.json` (`preflight.log`).

The endpoint helper passed in `1794137482677442907-5.json`. The selected-step
closure and raw representative application helpers passed in
`1794137552465238078-5.json`; encoded core lifting passed in
`1794137619485512036-5.json`; the witness-free actual edgeLift rule passed in
`1794137698071226445-5.json`. The main selection package and four exact aliases
passed in final receipt `build-reports/1794137735574407872-5.json`
(`exact-07.log`).

Three failed candidates are retained under `failures/`, with their immutable
numeric receipts and associated compiler logs. The two endpoint attempts
needed the correct namespace for conjunction helpers; the step attempt needed
the namespace containing renameInto. Repairs changed only new proof files.
No frozen statement, supplier source, target, compiler setting or resource
limit changed. The exact aliases are:

- `certified_application_step_closure_exact`.
- `certified_encoded_quotient_edge_lift_exact`.
- `certified_quotient_edge_lift_exact`.
- `selected_certified_quotient_edge_lift_exact`.

All four printed exact-alias closures and all 28 namespace audit entries
(24 supporting entries plus the four exact aliases) use only `propext`,
`Classical.choice` and `Quot.sound`. No proof placeholder or additional axiom
is part of the accepted sources.

## Focused source closure and unchanged resources

The focused exact-gate/preflight import closure contains 1,279 local modules,
including meta imports. Each current source SHA256 matches a successful row
in one of 107 immutable numeric receipts. Prior matching supplier receipts
are reused; this is not a fresh whole-closure or full-root build.
`SOURCE-PINS.json` records all current source hashes. The local
`closure-receipts.local.json` retains corresponding receipt and log hashes.
All 57 frozen/prerequisite/manuscript/correspondence pins match exactly.

The evidence collector explicitly excludes `latest.json`, all symlinks,
and nonnumeric receipt filenames; accepted receipt filenames must match
`[0-9]+-[0-9]+.json`. Raw receipts, compiler logs, failure snapshots, local
absolute-path evidence and the collector remain local, outside the portable
publication allowlist.

The portable checker invocation, run from the formalization directory, is:

    python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftStatementChecks

The profile retained 2,048 MiB heap, 1,536 MiB process-tree RSS cap,
2,048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall seconds.
Peak successful component RSS was 1,081,832 KiB; the maximum across reused
successful closure receipts was 1,176,760 KiB. The pinned upstream cache was
used with no upstream rebuild, dependency change or resource increase.

The final compiler session exited with code zero and was reaped. Both shared
locks were observed free before slot release; see the local slot-release
record. No further compiler work is planned by this worker. Post-checkpoint
review and publication remain with the coordinator.

## Exact scope

The checked core is `InternalQuotientEdgeChecker.checker` on the exact
`InternalCertifiedSourceGuardSelection.edgeData`. The selected typed checker,
recursive validity V, normalizer N, success test H, combine C and tagged
representatives all share the same original finite leaves.

Endpoint presentation reuses the previously checked theorem through a
proof-local adapter built from those same leaves. Selected-step closure
derives target-parent source validity using the duplicate endpoint (t,t,a).
It derives parent H from actual child H, internal total N/C graphs and
certified-fold closure. Representative congruence uses actual payload
transport and N(argument)=argument, never an assumed representative=N law.
Six internally scoped actual query outputs eliminate all raw certificate and
application witnesses; original edgeLift commutation retains the supplied
certificate exactly. Fixed-context source selection occurs before all
types/terms. No external calibration is reflected on symbolic inputs.

This is not output typed-invariant exposure, the outer typed-edge wrapper,
full-context dispatch, context-uniform/path lifting, the malformed outer
pathValue case, the full CertifiedApplicationLift premise, multiset/constructor/
lambda/substitution or all-term accessibility. The source register is unchanged.
Frozen artifacts retain their historical pre-proof state. No full-root,
remote-CI or Git claim is made.
