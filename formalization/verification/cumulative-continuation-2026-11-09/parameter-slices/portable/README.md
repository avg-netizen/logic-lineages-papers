# R007: original composite parameter-slice congruence

**Accepted supporting component, 9 November 2026.** The unchanged frozen
`ParameterSliceTargets.ActualOriginalCompositeParameterSliceCongruence` is proved
and checked by the exact alias `ParameterSliceStatementChecks.parameterSlice_exact`.
The exact alias and all 13 proof-namespace theorems use only `propext`,
`Classical.choice` and `Quot.sound`. Independent final review accepted the
statement, current source hashes, actual axiom output and native provenance.

## Scope

For one arbitrary Data and arbitrary natural parameters p and q, equality of
the three all-input callback slices (old representative, source validity and
membership) gives equality of the actual transition, representative, scalar,
typed, foldN and actualJ Programs on all raw inputs. No validity, typing,
successful-run, canonical-parameter or context encode/decode-inverse premise
is added. The original fold transfers through equality of callback functions.
The actualJ proof normalizes its raw argument once, then uses one combine.

This is native algorithmic congruence. Internal reflection, original all-input
source-pair calibration, the unqualified application lift and full ID1
completion are not claimed. No numbered source theorem, target-register row
or root import is changed. Only the two proof/check Lean files are new; the
three frozen specifications and accepted suppliers remain unchanged.

## Verification and provenance

The target-only native preflight passed before proof authoring. The first
candidate check passed. The complete 1,230-module local import closure has
a source-matched successful native row, distributed as follows:

- Receipt 1794217383057934424-2: 1,076 selected successful rows.
- Receipt 1794219754604424669-2: 2 selected successful rows.
- Receipt 1794219897721243520-2: 74 selected successful rows.
- Receipt 1794220200835732408-2: 78 selected successful rows.

Receipt 1794219897721243520-2 **failed overall** at the unrelated
OuterArithmeticProof source. It contains 122 successful rows and one failure.
Only 74 individually successful source-matched dependencies of this packet
are used. This receipt is not represented as a successful invocation.

The final invocation compiled 76 accepted dependencies and the two new
sources. All 78 rows passed. Peak final process-tree RSS was 1,407,108 KiB.
All checks retained the same 2,048 MiB heap cap, 1,536 MiB RSS cap, 2,048 MiB
free-memory floor, one thread and per-module 90-second CPU/180-second wall
limits. There was no upstream build, full-root check or remote-CI check.
The native process was reaped and both compiler locks released.

`SOURCE-NATIVE-COVERAGE.json` records the exact successful-row union and
numeric receipt identities. `NATIVE-CHECKS.json` gives the frozen preflight
and new-source native rows. `AXIOMS.json` and `AXIOM-EXCERPTS.txt` preserve
actual theorem axiom output. The remaining metadata records source
correspondence, the original freeze and accepted source hashes. This packet
contains no cache artifacts, private host paths or full raw native logs.

A focused reproduction, with the pinned toolchain and existing upstream
cache available, uses the repository checker with the same profile:

```sh
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceStatementChecks
```
