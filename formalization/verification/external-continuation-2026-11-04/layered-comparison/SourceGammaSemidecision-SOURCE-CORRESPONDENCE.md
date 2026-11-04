# Encoded-list search and fixed-control co-RE upper bound

Target-only proposal for paper09 hardness.tex lines 316–319: enumeration of all positive raw ground tuples and semidecision of a failed universal strict comparison. The independent restricted coded language and its existing Gamma semantics are unchanged.

The witness representation is the existing Encodable (List Nat) instance. A failed list decode yields false. Successful decoding passes the list unchanged to the accepted counterexample predicate, including its exact length/positivity checks, invalid-query acceptance and evaluator-None rejection. Encodable.encodek supplies every finite list; no assertion that all natural codes decode, or that re-encoding a decoded noncanonical code returns that code, is needed.

Search uses Nat.rfind on a total Boolean test wrapped in Part.some. ExactSearch identifies its domain with the complement of the independent restricted language and specifies the least encoded witness. This is least in natural code order, not by list length, valuation magnitude or runtime. On language members the search is undefined.

For each fixed b, the existing actual Gamma evaluator makes the test Computable. Partrec.rfind and Partrec.dom_re establish partial recursiveness and the standard Lean REPred of the complement. UniversalNormalForm gives an explicit computable predicate with one universal natural quantifier, the scoped Pi-zero-one/co-RE upper-bound formulation. It does not introduce or presume an unverified hierarchy API.

This supplies a computable upper bound, not the manuscript's stronger wording that collapse is fixed finite iteration of a primitive recursive control. No PR evaluator/search value or runtime bound is asserted. No total search, reverse many-one reduction, completeness theorem, weak-comparison theorem, arbitrary ordinal valuation extension, or publication/register promotion is included.
