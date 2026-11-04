# Positive valuation coverage and exact counterexamples

Target-only proposal toward paper09 hardness.tex lines316–319. This is the explicit computable witness predicate, not yet an rfind semidecision or completeness theorem.

PositiveCoverage proves both directions between finite positive lists of exact length n and positive raw component valuations of replicate n ground. Surjectivity is required: every actual raw valuation is represented, not merely every supplied list interpreted.

Counterexample immediately returns true for an invalid independent restricted-syntax code, because such a query is outside the language. Otherwise it unpacks the original (n,left,right) tuple, checks exact list length and positivity, evaluates both codes, and compares rightValue≤leftValue. A missing result returns false, never a semantic failure certificate; checker soundness and restricted evaluator totality establish that valid tested tuples have successful results. Failed decoding after a successful checker is also false and proved unreachable as needed.

FixedComputable is for each fixed b. ExactCounterexample is the complement of the unchanged independent restricted Gamma language, with the exact left<right orientation; generated queries store R,L but this general predicate does not swap arbitrary queries.

No unbounded search, reverse many-one reduction, full completeness, weak comparison, runtime or publication claim. Existing Member, source syntax and assignments are unchanged.
