# Paper 16: original open stable inserted-row selection

Paper 16, `sections/ordinals.tex`, lines 143–153, assigns an inserted
occurrence to a removed dominator's origin. These concrete PR passes
scan the literal scratch list of original row codes. Both passes query
the same fixed scratch removed pool with its actual `scratchMember`
program. The queried key is `field 1` of the very row term under
consideration, the original tag-4 dominator selector. The positive
pass keeps that entire original row, not the decoded target alone;
the complementary pass keeps that entire row on rejection. Neither
pass changes or consumes the common removed pool, so later occurrences
can reuse the same dominator. Both recurse using the original raw-list
recursor and prepend to preserve relative order on each side.

`NumberedWindowInternalOriginRowsFilterStepProof.exact_OpenOriginRowStep`
checks four bidirectional branch laws on arbitrary ordinary-arithmetic
terms under an actual field report and positive/negative membership
derivation. `NumberedWindowInternalOriginRowsFilterRecursionProof` has
aliases `exact_OpenOriginRowFilterNil` and `exact_OpenOriginRowFilterCons`:
the same applied original base and the actual existential tail-result
equation at each literal physical input cons.

These are object derivation formulas, not numeric replay. They do not
already prove the two whole scans have the right side-local certified
all-row reports, the count-recombination law or the full open
`CertifiedOriginSplit`.

Frozen Lean source hashes (SHA-256):

    98f132e93f1a860583db2393d2c5b0003b83f43e7071bd40c3ecb269e60c7027  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOriginRowsFilterRecursionProof.lean
    16244e3e4c17f7a67afb1eaf0787b233a2637774c943ff60bf01b5301e4441d3  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOriginRowsFilterStepProof.lean
    5fac3dcfc61f00ee9f85ce38f28705b41653f01dae15f0d06ce99e587d71237b  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOriginRowsFilterTargets.lean
