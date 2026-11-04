# Decoded source restrictions and nonhalting reduction

This pays the source restriction clauses of paper09 hardness.tex lines 281–286 and 308–314 for the established strict-comparison reduction. It does not assert the upper-bound/completeness argument at lines 316–319.

RestrictedSyntax is an independent property of a decoded scalar query, not an image-of-constructor predicate. Actual ground-typed witnesses must exist in canonical replicate n ground context, have the exact decoded source codes, satisfy the existing recursive Fragment (only 0/S primes and ground binders), and satisfy the existing InternalLevelBound 1 on full typeSupport. Failed decoding or absent witnesses does not satisfy the predicate. Ground free names are ensured by the canonical context.

ExactSyntaxClass identifies this decoded predicate with the literal syntactic conditions on any source pair in an all-ground context; fixed-context codec adequacy prevents different witnesses from changing the class. GeneratedRange proves the complete explicit output b e always lies in this syntax class, independent of halting, using the accepted actual aggregate fragment and internal-level bounds. The output orientation stays R,L, so both paired restrictions are correspondingly swapped from aggregate L,R.

RestrictedManyOneReduction uses the same explicit primitive-recursive e-to-output map for each fixed b. Nonhalting is equivalent to restricted Member(gamma b), defined as RestrictedSyntax and the independently established Gamma coded strict language. This is a genuine restriction of the target language, not a change to its semantics or a test of the reduction's range.

No upper semidecision bound, completeness classification, weak comparison, other valuation domain, source size/runtime bound or whole theorem promotion is claimed. All original sources/frozen files stay unchanged; verification-only, no export.
