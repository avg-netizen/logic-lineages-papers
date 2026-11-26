# Independent final reproduction: complete whole-block projector (root, local continuation)

Accepted as a supporting endpoint: `WholeBlockProjectorTargets.Full`, the
four-family conjunction (Semantics 9, Dispatch 6, Projection 6, Initialized 2;
23 original contracts). Root did not author the comparator or the proofs; they
are the previous coordinator's staged assemblies at checkpoint ff2e5a5b8, and
no source file was changed locally.

This closes the two items the earlier reviews left open. (1) Fresh full
gate: the complete 718-module closure was compiled from source on the local
host under the unchanged Mathlib profile (2048/1536/2048, one thread, CPU
90/wall 180) with no failure or repair; full alias gate receipt
1795036071718645424-2026798, exact alias
`StandardControlCurrent.StatementChecks.fixed_wholeBlockProjector` on
propext, Classical.choice and Quot.sound only. (2) Independent reproduction:
all thirteen frozen pins recomputed and match; compiler-free recursive
evidence (WHOLE-BLOCK-PROJECTOR-EVIDENCE.json) verifies 718 source-matched
modules with zero errors.

Scope and the mathematical supplier audit are those of
WHOLE-BLOCK-PROJECTOR-PRE-SCOPE-REVIEW.md, -PLAN-REVIEW.md,
-AUTHORED-STAGES-SCOPE-REVIEW.md and -SUPPLIER-MATHEMATICAL-REVIEW.md, which
reported no blocker; this review adds the native and evidence facts and did
not repeat the hand audit.

Not covered: the one-binder HFree Matrix composition, arbitrary SourceFormula
alternation and shadowing recursion, the closed decision, expanded Phi/H
elimination, and the numbered statements `m:thm:snyatkov`, `m:thm:common`,
`m:thm:balanced`. No full-root or CI claim.
