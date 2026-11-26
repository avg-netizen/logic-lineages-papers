# Active minimum and Object rank transport checkpoint

Status: checked supporting checkpoint, 11 November 2026 (America/Chicago).

Base: `af61da124919d10934aa8e56a49da7ac848e770f`, on the existing
`formalization/cumulative-continuation-2026-11-09` branch.

Seven exact supporting contracts in nineteen new Lean files pass native
compilation, their frozen type comparisons and standard-axiom audits. All new
source bytes are unchanged from the pre-compilation candidate snapshot; no
native proof repair was needed.

| Statement gate | Exact contracts | Result |
|---|---:|---|
| `OriginalActiveObservedMinimumStatementChecks` | 3 | checked |
| `OriginalRawObjectRankTransportStatementChecks` | 2 | checked |
| `OriginalCanonicalizedObjectRankTransportStatementChecks` | 2 | checked |

The active-minimum contracts establish least-hit minimality for the actual
once-guarded initial representative, calibrated retention of the complete
previous Package, and global selection at one shared minimum-input tuple.
The final traversal, packed-fold and Object rank laws use that same tuple.

The raw Object contracts prove shift rank equivalence and erasure rank
nonincrease for every raw code, including malformed codes and empty decoded
contexts. The canonicalized contracts carry these conclusions through the
actual unchanged final Object program. They use the original outer window and
input typing; contextual erasure retains its genuine context-cons witness.
No typing or fixedness of the raw transformed Object is assumed.

See [source correspondence](SOURCE-CORRESPONDENCE.md),
[exact gates](GATES.json), [exact aliases](EXACT-ALIASES.json), and
[frozen source hashes](FROZEN-SHA256SUMS). All 238 inherited frozen source hashes
are retained, with nine new frozen specification files.

The [native evidence report](runs/20261112T023617.571214Z/REPORT.json) verifies
all **3,230 local modules** in the focused closure, all seven exact aliases,
**6,387 recorded axiom declarations**, and **1,311 namespace audits**. The
selected native logs, successful receipt rows, source/object hashes, frozen
preservation and inherited-source preservation are stored beside that report.
Every audited declaration uses only `propext`, `Classical.choice` and
`Quot.sound`. The three separate specification preflights also pass.

The pinned Lean 4.32.0-rc1 toolchain and 1,069 upstream cache modules were
restored without an upstream rebuild; [acquisition](ACQUISITION.json) and
[source restoration](SOURCE-RESTORATION.json) record provenance. The fresh
checkout required a cold local dependency build. The subsequent contract run
reused 3,193 content-verified native modules and compiled 37 further local
modules. Both invocations completed without a native failure. Their complete
transcripts and original receipt JSON are retained in
`COMPILER-TRANSCRIPTS.json.gz` and `COMPILER-RECEIPTS.json.gz`.

All compiler work used the unchanged `scripts/check.py` with one serialized
worker, 2,048 MiB heap, 1,536 MiB observed process-tree RSS, 2,048 MiB free-memory
floor, 90-second CPU and 180-second wall limits. Peak observed RSS was
1,445.7 MiB, below the existing cap. The checked incremental cache is populated.

No full-root or remote-CI result is claimed. The original paper06 internal
accessibility endpoint remains pending; the register is unchanged at
171 checked, 2 inherited, 16 pending /189. Accepted mathematical sources,
manuscripts, dependency/toolchain pins, CI and the shared checker are preserved.

## Remaining mathematics

The next obligations include the original internal class kernel and
representative coherence, canonical cancellation, the erasure certificate
transformer, internal substitution/I/C and lambda/constructor integration, and
the original closed
`ContextUniformTargets.ActualContextUniformInternalAccessibility` derivation.
Rank preservation does not supply those missing transport laws. The manuscript's
separate transitivity obstruction remains unchanged.
