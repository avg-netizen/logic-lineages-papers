# Original level-two comparison: accepted bounded proof route

Three new Lean modules independently complete the unchanged original
paper08 `thm:leveltwo` target. One concrete uniformly computable solver
decides universal weak, WW-strict and equality comparison of actual
canonical assignments, with ground free variables and every internal
subterm and binder type bounded by level two.

The accepted declaration is
`LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedStatementChecks.full_internal_level_two_comparison`,
with the original frozen `Targets.FullInternalLevelTwoComparison` type.

The focused gate has 926 source-matched successful native dependencies:
923 unchanged inherited modules and 3 new modules. All 90 declaration
audits use standard axioms: 77 helpers and 13 exact aliases. Each of the
three stages passed the unchanged single-threaded 2,048 MiB heap,
1,536 MiB RSS, 2,048 MiB free-memory floor and 90 CPU/180 wall-second limits.
The highest stage peak was 1,568,468 KiB RSS.

All thirteen original LevelTwo files and the frozen target remain unchanged.
The original typed file's two RSS stops are retained; the new semantic,
witness and alias modules exclude that failed route. Their proof bodies
match the originals after explicit namespace qualifications and split imports.

This source-only checkpoint does not change the root or register. At its
preparation the register remains 171 checked, 2 inherited and 16 pending
out of 189. Numbered-statement adoption is a separate reviewed step.
Full receipts and raw logs remain local, outside the source publication.
No full-root build or remote-CI pass is claimed. See SOURCE-HASHES.json.
