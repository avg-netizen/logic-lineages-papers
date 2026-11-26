# Independent ClassCodes observations refactor review

Approved for coordinator native. Verified original archive4984d9bc5f74f9b75975a940a20bef877ee36f5eb6660905edea4fa625f8393b and both proposed current pins. All three public theorem headers unchanged; frozenBlock and matrixWitness proofs byte-identical. Only helper import and observationsSubst implementation changed.

Generic schema preserves exact ordered twelve conjuncts: eight output graphs at xs1..8, nonzero xs8, pairing(candidate,xs1,xs0), Fields, depth. Actual caller vector is rootType/types/heads/size/labels/bound/fuel/admitted in original order. Fields syntactic substitution premise is explicitly discharged using acceptedSubst of actual OriginalEnumerationFields.fields n at xs0,xs6,xs2,xs3,xs5,xs4. Depth premise uses actual boundSubst n xs0 xs7. No result/admission oracle or new public premise.

Generic proof uses existing graph2/negation/equality/conjunction substitution and numeral normalization, no axiom/reflection/AST or target change. All limits fixed. Native must establish exact definitional specialization; no performance/success claim yet, prior failure preserved. Reviewer ran no compiler.
