# Literal finite-window computability disjunction

Source: paper06 lines576–580 explicitly says arbitrary computable arguments abbreviate a finite disjunction of typed computability formulas over S, not satisfaction over all simple types.

windowFormula is an actual finite list recursion in the accepted general first-order language. Free coordinates are context,typeCode,value. Each list entry tau contributes literal typeCode=typeNumber(tau) conjoined with the accepted fixed-type formula reindexed to context/value. The empty list is false; cons uses disjunction. No evaluator/satisfaction predicate is introduced into the language. The external formula family is supplied by the accepted fixed-type construction, not by a new semantic axiom.

Target1 calibrates the literal assembly for any formula family to existence of a type occurrence in S with exact code equality and that formula's truth. Target2 supplies the actual C_tau family, retains its individual calibration, proves the window iff to exists tau in S with exact code and semantic Computable, and explicitly rejects any code whose actual decodeType returns none. Rejection follows from accepted type numeric roundtrip. No assumption that every natural decodes is used.

S may be empty, contain duplicates, be unsorted or fail subtype closure. Empty assembly is false; duplicate branches do not change existential truth, and multiplicity is not silently used as a new predicate. Semantic C retains its typedness/partial-application clauses. The statement is all-code standard-N calibration, not computability under substitution, all-term C, ID1 derivability, or original transitivity/WF. Proof absent until exact review/freeze.
