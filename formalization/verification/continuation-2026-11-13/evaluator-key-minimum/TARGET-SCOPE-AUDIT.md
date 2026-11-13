# Independent target audit: evaluator-key minimum

Reviewed new EvaluatorKeyMinimumTargets.ActualMinimumEquality source; not a
claim of proof acceptance. It retains the explicitly new EvaluatorKeyPut
minimumInputs tuple. Premises are the two actual Domains, SAME actual evaluator
output, and the two actual minimum graphs. There is no native calibration,
equal scan bounds, supplied candidate row, or full-fold equality premise.

The intended original route is genuine least-hit comparison, not identical
scan length. Derive each minimum's own hit and exclusion of every strictly
smaller candidate from the original internal minimum theorem. ActualRows
transfers the first output's hit to the second row and vice versa. If out is
strictly below otherOut, the second minimum's exclusion contradicts the
transferred first hit; the reverse strict inequality uses the first minimum.
Internal trichotomy yields equality. This orientation requires no out<=other
seed premise: every value below that row's selected output is already within
its own seed bound. Reflexive target acceptance guarantees a hit at each seed,
so no unproved successful-search premise is needed.

The older OriginalAllPositionMinimumCoherenceProof.coherenceAt implements this
same argument but its AST wrapper is different (rank-observed/all-position
minimum). It is a proof template, not a theorem that can be applied by silently
identifying tuples. New minimumFacts must be derived for the literal
OriginalTransparentMinimum.minimumInputs/reflexiveClassTest in the frozen
EvaluatorKeyPut definitions, with the actual target/domain facts.

No bound-orientation or hidden-calibration defect found in the proposed target.
It remains a once-minimum theorem only, not final traversal/fold equality or
Object cancellation. Global register is unchanged.

## Reviewed snapshot (not an acceptance certificate)

```text
c7630ba2744804c27412a881823d1d119973643551a71e40e0f2792f34f52e27  EvaluatorKeyMinimumTargets.lean
084f3554bd58d223cba2ec88b743abd829f37e1fc939e53ed9f9e4b856ea49a9  EvaluatorKeyMinimumPreflight.lean
9fb36e2cd07dabf72f3919b52b14b6120f22dddc265a5a9e02ade5f9414a86e7  EvaluatorKeyPutDefinitions.lean
38ba2784c205cc1221980758806d4f68a196ce151c9044513c388223f67dd8f2  EvaluatorKeyPutTargets.lean
```
