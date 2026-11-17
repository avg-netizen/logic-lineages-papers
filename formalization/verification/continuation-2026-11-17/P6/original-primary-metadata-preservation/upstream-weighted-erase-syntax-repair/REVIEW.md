# Independent WeightedErase syntax repair review

Status: SEMANTICALLY APPROVED; native acceptance is separate.

Reviewed all four repair modules against the preserved original and actual WeightedErase/EraseInvariant definitions. All ten original public theorem headers (including simp attributes) are byte-identical. Original formulas remain in their original definition files; no target replacement or assumption was added.

The helper effectSchema abstracts only binary merge. fieldsSchema abstracts the erase-state graph, pairing graph, weighted fold and weight graph with precisely the original conjunction nesting, argument order and output positions. matrixSchema retains the original seven bound coordinates needle/acc/bit/rest/total/remainingWeight/needleWeight; allSchema retains the original allBlock. Instantiation uses exactly Erase.state, InternalPairing.pairing, OriginalBoundsRecombination.merge, Fold.weighted weight and the same weight. Thus schema unification requires only unfolding formula wrappers, not substituting a different algorithm.

The generic substitution proofs use existing graph/program substitution and logical connective laws. The allBlock proof lifts the substitution through the seven binders. matrixSchemaWitness substitutes the matching seven-field vector and eliminates the lifted free-variable embedding. Remaining renaming, predicate instantiation, below renaming and predicate lift wrappers preserve their prior arguments and proof route. No oracle, metadata premise, arithmetic invariant, classical decision shortcut or new axiom is introduced.

No compiler was run by this reviewer. Native exact-type and standard-axiom closure must pass under unchanged resource caps before this repair is accepted as checked. Hashes are recorded in REVIEW-PINS.json; any later source repair requires reconciliation. This is proof organization only and earns no independent mathematical endpoint credit.
