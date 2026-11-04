# Binder-aware positive syntax transforms for later disjoint tags

Paper06 lines569–571 proposes combining separate unnested operators by disjoint numerical tags. These two prerequisites transform the accepted actual Positive syntax, not merely semantic predicates.

Relabeling maps arithmetic leaves, predicate terms and arithmetic guards, lifting free-variable maps through Sum.map at each universal binder. Tagging changes only the new predicate's argument to the literal arithmetic term 2*x or 2*x+1, leaves every arithmetic carrier/edge guard unchanged, and traverses all binders. Both transformations preserve positivity by their return type and compile through the same actual extended first-order language.

Exact standard-N calibration handles arbitrary free-variable maps and both Boolean tags. The combined operator, tag partition/isolation, fixed point, ID1 axioms/derivations, accessibility and well-foundedness are separate unpaid work.
