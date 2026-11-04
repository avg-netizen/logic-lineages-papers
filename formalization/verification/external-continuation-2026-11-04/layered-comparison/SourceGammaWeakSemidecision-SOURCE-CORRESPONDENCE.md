# Encoded-list semidecision for independent weak comparison

This scoped upper-bound component corresponds to paper09 hardness.tex lines 316–319. The independent SourceGammaWeakCodedReduction.Member and its positive natural raw valuation/finite Scalar semantics are unchanged.

The natural witness code is decoded with the standard Encodable (List Nat) instance. Failed list decoding yields false; a decoded list is passed unchanged to the accepted weak counterexample predicate. In particular, successful finite values violate weak order exactly when right<left; invalid query syntax remains an immediate counterexample, while evaluator None is not a counterexample. Every finite list has a code by encodek, without requiring all natural codes to decode canonically.

Nat.rfind searches the total Boolean test wrapped in Part.some. ExactSearch identifies its domain with nonmembership and its result with the least natural witness code. This is not a least length or least runtime assertion. Search is undefined for members.

For each fixed b the joint query/witness test is Computable, its search is Partrec, and the complement is Mathlib REPred. UniversalNormalForm explicitly gives a computable predicate universally quantified over natural witness codes. No named hierarchy API, total-search theorem, PR evaluator, reverse reduction, weak completeness classification or unrestricted source theorem is included. No export or register promotion.
