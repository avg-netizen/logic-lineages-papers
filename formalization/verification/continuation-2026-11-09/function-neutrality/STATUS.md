# Accepted — canonical function neutrality and original step reflection

**Six exact supporting contracts pass in 24 new Lean modules.** This
continuation extends `d58037354fc4e33475929f30fdf97ed27070d663` on
`formalization/cumulative-continuation-2026-11-09`.

The SAME canonical fold now preserves and reflects the original neutral
application test: an application whose actual function child is not a lambda.
Two raw sources with a common actual canonical output have the same test.
The original raw-step checker can consume neutrality at its source's canonical
output and recover literal same-type bottom or an accepted function-child
step, retaining the original certificate, parameter and raw argument.

| Frozen exact target | Checked result |
| --- | --- |
| `ActualOriginalFunctionNeutralityRefinementEquality` | The concrete representative guard leaves every original raw output unchanged and preserves all-input calibration. |
| `ActualOriginalFunctionNeutralitySelectedPreservation` | The selected bounded descent preserves and reflects every symbolic value of the original neutral test. |
| `ActualOriginalFunctionNeutralityFullFoldPreservation` | The SAME full canonical fold preserves and reflects that test, including its final selected leaf. |
| `ActualOriginalFunctionNeutralityCanonicalComparison` | Two valid raw sources with one common actual canonical output have equivalent neutral-test graphs. |
| `ActualOriginalFunctionNeutralityGlobalSelection` | One final tuple retains the full calibrated Package, root fields, full-fold neutrality, neutral-bottom law and both variable Object laws before all source windows. |
| `ActualOriginalFunctionNeutralityStepElimination` | Canonical-output neutrality supplies the raw source premise for the original same-type-bottom or full accepted function-child split. |

## Proof construction

The observer is the existing `OriginalNeutralLeaf.neutralTest`, placed in a
concrete representative guard before the established shape pipeline. Native
primary application-view and lambda-shape results prove that the guard is
redundant on every original raw input. Inactive and malformed inputs retain
the complete original output. The internal derivation reads the actual guard
Program and propagates its invariant through the shape, variable, spine and
bottom wrappers and the original bounded-descent iterator.

For an open canonical application, the original eliminator binds both actual
child-fold outputs and their certified graphs. The previously checked
root-field theorem reflects the actual function child's lambda tag through
its own fold. Original constructor graphs then compute equal neutral tests
for the raw parent and rebuilt application. The selected-leaf invariant
supplies the final step. Closed roots use the existing closed-leaf equation.

The global tuple is literally

```lean
OriginalConstructorShape.finalInputs
  (OriginalFunctionNeutrality.refineInputs p)
```

Every package, root-field, neutrality and variable law concerns that same
final source. The raw-step consumer uses its actual accepted certificate,
window, type, endpoint and parameter. No native semantic oracle or assumed
whole-fold invariant enters the internal derivation.

## Remaining boundary

The final recovered relation remains `graph2 (leaf data) out rebuilt parameter`.
This packet does not identify `out` with `rebuilt`, or prove equality of the
corresponding canonical children of applications with a common full-fold
output. Canonical component coherence remains necessary for quotient neutral
inversion and neutral saturation.

Arrow computability, all-type variable C, lambda/substitution, multiset and
numbered-constructor closure, and closed all-term context-uniform accessibility
remain pending. Paper06 `lem:id1` is not promoted. The numbered register stays
**171 checked, 2 inherited, 16 pending / 189**.

## Verification

The exact gate is `SourceComputabilityCompletion.OriginalFunctionNeutralityStatementChecks`.
All six exact aliases and 86 additional namespace declarations passed
native axiom audits using only `propext`, `Classical.choice` and `Quot.sound`.
Every one of the gate's 1,871 local sources has a matching successful
native compilation row; the separate specification preflight gives 1,872
source-matched modules in total. This fresh checkout also rebuilt the inherited
1,842-module constructor-shape checkpoint successfully. No full-root or remote-CI
pass is claimed.

Final receipt: `build-reports/1794291587284344577-5.json`. The unchanged serialized checker used
one worker, a 2,048 MiB heap cap, 1,536 MiB RSS cap, 2,048 MiB admission floor,
and 90 CPU/180 wall seconds per module. Peak successful new-module RSS was
1,163,280 KiB. The global proof was split into smaller
parameterized package, field and variable-law modules after one RSS stop;
no resource limit or frozen target changed.

All 10,277 inherited mathematical Lean sources and three frozen specification
files are unchanged. The root aggregate adds only the new gate import. The
checker, toolchain, dependency manifests, manuscript and CI are unchanged.
All owned compiler jobs have completed.

`ACCEPTANCE.json`, `AXIOMS.json`, `FROZEN-PRESERVATION.json` and
`exact-checks.log` record acceptance. `ATTEMPTS.json` and `failed-attempts/`
preserve the six unsuccessful attempts and their repairs. Source pins,
complete source-matched native rows and gate/preflight receipts are losslessly
compressed with hashes in `EVIDENCE-ENCODINGS.json`.

See [source correspondence](SOURCE-CORRESPONDENCE.md) and
[concrete next steps](NEXT-STEPS.md).
