# Actual variable-or-bottom headed spines

Draft requested 2026-11-04 12:19 UTC. Exact review required before comparator/freeze or proof. Verification-only, no export.

Paper06 lines583–589 claims variables and bottoms computable using function-side application behavior. These targets establish a literal syntactic prerequisite, not that computability conclusion. InertSpine includes precisely variable or bottom roots followed by any finite number of explicit applications. Argument types and terms are arbitrary, with no argument normalization or computability premise.

The rank is 1 on a variable, 0 on bottom and all other roots, and adds 2 for each application on the function spine. Hence variable-headed depth d has rank 2d+1 while bottom-headed depth d has rank 2d. The Bottom rule may change a variable head into bottom without shortening its surrounding spine; depth alone would not strictly decrease. The head-bit rank handles this actual transition.

The first target proves InertSpine equivalence and unconditional rank equality under the existing full WindowPrimary relation, including symmetric/transitive closure and its application-argument equivalence context. It does not assume the inputs are inert for the rank equality. The second target proves inertness preservation and strict rank decrease for the actual WindowStep from an inert source. Positive steps have only function-side application contexts, not application-argument contexts. Whole-term bottom reduction is handled because every nonbottom inert term has positive rank; bare bottom has no step.

No subtype closure, finite signature, confinement or precedence assumptions are needed for these literal syntax statements. Later numeric quotient accessibility would need its own exact confinement/representative/trace bridge. That bridge, semantic least membership, variable/lambda computability, all-term accessibility, the invalid-precedence diagnostic, ID1 and original-order transitivity are not included.
