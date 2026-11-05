# Source-term graph checkpoint — 5 November 2026

**Accepted: eleven exact supporting targets in two gates.** Actual source
terms now have literal occurrence-row graphs with exact fresh allocation,
support, total domains, soundness, realization and uniqueness. Their finite
existential closure is equivalent to the original source-term value equation.
The complete postfix/numeric implementation is calibrated and primitive
recursive.

The source semantics use the existing actual `Phi`, unchanged original variable
indices and all repeated occurrences. The realization theorem preserves every
name outside the allocated interval. Soundness and allocated-node uniqueness
require no freshness hypothesis; realization and the existential equivalence
use the explicit fresh-allocation premise.

The final cumulative aggregate
`LogicLineages.ExternalCheckpoint20261105SourceIntroduction` passed in
[receipt 1793838387406023253-2](receipts/1793838387406023253-2.json).
All **133 local source modules** in its closure have successful receipts matching
their current SHA256 hashes. The eleven exact aliases passed actual transitive
axiom audits with only `propext`, `Classical.choice` and `Quot.sound`.
Compiler limits remained one thread, 2048 MiB heap, 1536 MiB RSS,
90 CPU seconds and 180 wall seconds per module. The new work's maximum observed
process-tree RSS was 1,167,748 KiB.

The [source-row package](../source-rows/STATUS.md) adds five further targets for
general source-formula introduction. This continuation therefore adds sixteen
targets; the branch has twenty-four including the preceding normal-form package.
The register remains **161 checked, 2 inherited and 26 pending / 189**.
There is no whole-source promotion.

The complete local-source hash and receipt map is in
[SOURCE-CLOSURE.json](SOURCE-CLOSURE.json). Raw logs, including the failed
proof attempts and target preflight syntax repair, are preserved in
[COMPILER-LOGS.json](COMPILER-LOGS.json). The acceptance scope is recorded in
[ACCEPTANCE.json](ACCEPTANCE.json), with the unchanged targets pinned by
[FROZEN-TARGETS.json](FROZEN-TARGETS.json). Read
[SOURCE-CORRESPONDENCE.md](SOURCE-CORRESPONDENCE.md) for the mathematical boundary.

The validation is the focused cumulative closure. No full public-root rebuild,
upstream rebuild or remote-CI success is asserted. Full existential normal
form, expanded elimination and arbitrary first-order source decision remain
pending.
