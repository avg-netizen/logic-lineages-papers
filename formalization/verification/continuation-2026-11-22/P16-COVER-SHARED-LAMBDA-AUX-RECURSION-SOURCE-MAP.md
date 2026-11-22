# Paper 16: one selected lambda-auxiliary recursion for each of V and measure

Status: frozen source, native gates pending. Exact two numeric step/calibration
pairs `exact_CoverSharedSyntaxStep`, `exact_CoverSharedSyntax`,
`exact_CoverSharedMeasureStep`, `exact_CoverSharedMeasure`, and physical
open row cuts `exact_OpenCoverSharedLambdaCut`, `exact_OpenCoverSharedAuxCut`.

The single actual shared dispatcher reads `cellHead` of the actual current
sparse key, compares with original literal 2, and calls one of two existing
whole physical four-input updates on the same `[prior,old,z,z]` tape. V uses
the original reselected lambda and auxiliarized syntax updates; measurement
uses the original reselected lambda measure update and the existing exact
chosen-aux measure update. Nonmatching arity or earlier-key conditions
still undergo their branch's original guarded fallback to the original
callback V or M. Malformed and copied zero behavior are retained numerically.

Numeric calibration is independent of the open case proof: either branch
has the exact original scalar bit/encoded measure against the same earlier
memo hypothesis. The aux measure step uses the existing exact chosen
binary calibration and original recurrence on the physical earlier reads.
Each selected recursor establishes its earlier reads by one original
strong induction on its own scratch table, not by relying on another
selected table being interchangeable.

The physical open cut uses the actual known literal current-key graph
and the original canonical-cell head selector at tags 2 and 6. At 2
actual equality supplies 1. At 6 actual object arithmetic derives
2<6 (literal original successor/addition rules), so the unchanged
equality program reports 0. Both directions retain exactly the same old
table, open key fields, output and tape, for either instantiated updater.
These are not whole selected-window graph equalities. A later child
lookup must recover the actual shared table, not apply older same-program
row evidence scoped to its own updater. No old V/M inversion, aggregate
own-cover, or protected typed closure is asserted.

## Frozen sources
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedRecursionTargets.lean`: `5373766077ea0b7d34b57522fc83d828eba7b828253c74c615541b7270d46404`, 1128 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedSyntaxNumericProof.lean`: `585d45d39d3353032cf487b54a8bf1341d1231c0cbe1759d107c8cdc3df3b61a`, 1178 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedMeasureNumericProof.lean`: `f3bf1d1202fe332ac49a77fb8f5beb41a45324ede9c170318ac2768d07b81a6e`, 1181 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedRecursionOpenCutProof.lean`: `0bdb91db432cfcf9e783e5abdbf5b52150fea1264c234e8189f6435e43739f93`, 1263 local modules.
No explicit Hydra or Linarith in these static local import closures.

## Principal exact origin pins
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverAuxSyntaxNumericProof.lean`: `3d6cd9ec4330437fd2794a68f2d2db3304e0e8638d99dacddda49e681fc00090`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLambdaSyntaxRowNumericProof.lean`: `e2be9aec69fb17ea43502b495c9cd17e5bf4779e25484da0c9c36fa2b530cbf3`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLambdaMeasureRowNumericProof.lean`: `0043069f8e494e8dd7046c21b461ba98dc64dc6400c338ab862eb735ee2b51a2`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAuxMeasureStepChecks.lean`: `9c5d9292ce0dd4a87a5d96e2dd02623f97f81fd31b26bf086c9914dad98082be`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAuxMeasureMemoChecks.lean`: `1e35ad948d86f82759007047ef226f2def380104fed0af3a87e9a53013e3a83f`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalChosenAuxMeasureCombineNumericProof.lean`: `25192a6530336b734965007425d30aacbc242d6b57a85c020ee88364a37c074f`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof.lean`: `717c863324e5effc3544c169eb6119f6bd9bca185b2e6a712f486f8e3087d298`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAuxMeasureOpenDataProof.lean`: `43153b983eecf710e1d58cbb9065ef55d14ffd8d4b85f359d3b920b456bc039c`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalSparsePathEnvelopeOpenCellProof.lean`: `c617c99b5dc815b1d781f7af9e7bf035ad65bc37e18e4aa4482bbadc0bdd52e6`.
