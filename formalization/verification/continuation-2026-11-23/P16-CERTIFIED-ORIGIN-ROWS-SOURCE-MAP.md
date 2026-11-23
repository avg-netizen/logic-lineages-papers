# Paper 16: assign actual numeric replacement rows to removed origins

Paper 16, `sections/ordinals.tex`, lines 143–153, assigns each newly
inserted occurrence to a removed dominator's origin. The row domain
here is the actual `NumberedWindowDirectAlgorithm.Entry`, with the
same `(target,dominator,cert)` fields used by `directLists`. The
pointwise premise unpacks the direct checker’s row condition: the same
dominator is present in the removed tape and the same positive check on
the given certificate and target succeeds.

`exact_OriginRowAssignment` assigns each whole original row to one side
and keeps its fields unchanged. It never consumes a removed occurrence.
A single removed occurrence can dominate multiple rows, just as in the
original checker. The output permutation preserves every original row
occurrence, including duplicates. The two side-local row checks use
their respective actual removed lists, not an aggregate membership
hypothesis.

`exact_OriginTargetRecombination` transports the target field by mapping
the row permutation and then reorders the kept and inserted
occurrences. The original accepted target tape permutes exactly to the
two projected side targets appended in order.

Exact gate `LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRowsProof`.
This is numeric list mathematics, not a proof for arbitrary open
arithmetic codes, reconstructed raw side certificates, or full original
`CertifiedOriginSplit`.

Frozen Lean source hashes (SHA-256):

    5d8e06386ef0af44be6a418944687f6f382a6399f2709a43ae4797305cf532b6  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginRowsProof.lean
    d0894337a3848175ba7f41b115778d7e99c8d460a79ec49357d3d74556aaf05b  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginRowsTargets.lean
