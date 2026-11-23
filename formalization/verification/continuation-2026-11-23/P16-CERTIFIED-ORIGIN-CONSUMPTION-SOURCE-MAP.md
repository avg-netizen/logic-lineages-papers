# Paper 16: occurrence-sensitive kept/removed origins on numeric tapes

Paper 16, `sections/ordinals.tex`, lines 143–153, requires labelling the
removed occurrences by component before assigning new occurrences to
dominators. This exact lemma derives the first split on the physical
lists of natural-number entries used by
`NumberedWindowDirectAlgorithm.directLists` and its split-observer
calibration `NumberedWindowInternalDirectCoreNumericTargets.CountFit`.
Its input is `List.Perm (left ++ right) (kept ++ removed)`, the actual
permutation once the numeric union and source partition are composed.

For each kept-tape head, the proof uses membership only to select a side.
It consumes exactly one matching occurrence via `List.erase`, preferring
the left side if both have a match, and cancels a common head from a
`List.Perm` proof. The residual sides are the removed split. The output
reconstructs the full left and right source tapes up to permutation, and
the two recombined kept and removed tapes up to permutation. Equal values
can be represented on both sides, and duplicate multiplicities are
preserved by all four output permutations.

Exact gate `LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginConsumptionProof`,
alias `exact_OriginConsumption`. This is finite natural-list mathematics:
not a derivation on arbitrary open arithmetic codes, not an assignment
of inserted rows, not a reconstructed direct certificate, and not the
full original `CertifiedOriginSplit`.

Frozen Lean source hashes (SHA-256):

    7ad272c80fced92a14e0a0dae34562676aac40013bb3e1ce79f00547a34b6bbe  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginConsumptionProof.lean
    cc9d277469348ce2f67f9bab5539ddcff89eee81f011820cfc1bc56df586879c  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginConsumptionTargets.lean
