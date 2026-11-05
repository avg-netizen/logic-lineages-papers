# Formalization checkpoint

The current cumulative continuation, 5 November 2026, adds **sixteen exact
supporting targets** for actual source-term graphs and general source-to-row
introduction. Together with the preceding eight row/domain/compiler targets,
this branch has **24 checked supporting targets in six gates**.
The register remains **161 checked, 2 inherited and 26 pending numbered source
statements out of 189**. Supporting targets do not count as whole-source
completions.

The source translation handles every original `SourceFormula` under every
valuation, preserves exact free-variable membership and named binder shadowing,
and has a literal primitive-recursive numeric compiler. Each atom's fresh graph
witnesses stay inside that atom; original negation and binder positions remain
in place. Full single-prefix existential normalization and arbitrary first-order
BASE decision remain pending.

The focused aggregate `LogicLineages.ExternalCheckpoint20261105SourceIntroduction`
passed. All **133 local modules** in its import closure have successful native
compiler receipts matching their current source hashes. All sixteen new fixed
target aliases passed actual transitive axiom audits using only `propext`,
`Classical.choice` and `Quot.sound`. No full public-root rebuild or remote-CI
pass is claimed.

**Known source issue:** a finite checked counterexample refutes transitivity
for the local source06 relation. Read the paper's
[mathematical status](06-godel-t-termination-ordering/STATUS.md). No error in
Kop's published theorem or unique repaired convention is established.

Read the [current checkpoint](formalization/verification/cumulative-continuation-2026-11-04/source-rows/STATUS.md),
[exact register](formalization/TARGETS.json),
[source correspondence](formalization/verification/cumulative-continuation-2026-11-04/source-rows/SOURCE-CORRESPONDENCE.md),
[term-graph evidence](formalization/verification/cumulative-continuation-2026-11-04/source-term-graph/ACCEPTANCE.json)
and [source-introduction evidence](formalization/verification/cumulative-continuation-2026-11-04/source-rows/ACCEPTANCE.json).
The cumulative branch is `formalization/cumulative-continuation-2026-11-04`,
starting from merged main `ba2dec0`; this checkpoint continues the accepted
`eb0dd98` normal-form package. Prior pause and publication records retain their
historical scope.
