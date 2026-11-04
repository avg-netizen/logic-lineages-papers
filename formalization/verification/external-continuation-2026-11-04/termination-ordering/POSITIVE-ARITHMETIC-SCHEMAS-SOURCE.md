# Literal parameterized closure and leastness schemas

Source: paper06 positive arithmetic operators and prospective ID1 leastness use. The schemas are actual existing-language formulas, not declared axioms or finite derivations.

Free variables alpha are parameters. Body has free variables alpha+Fin1, the final singleton being the current object x. Closure is all x (body(I,params,x) implies I(x)). Leastness at an arbitrary formula theta(params,x) is [all x (body[theta/I](params,x) implies theta(params,x))] implies [all x (I(x) implies theta(params,x))]. Replacement uses the accepted liftPredicateFormula theta before substitution into body, so the body object binder is never mistaken for a replacement parameter. Theta may itself contain I with either polarity.

The two targets calibrate truth under arbitrary standard-N predicate P and parameter valuation v. Closure becomes exactly the semantic closure implication. Leastness becomes exactly the assertion that whenever the theta-defined set is closed under the body operator (interpreted with that set), P is contained in the theta-defined set. Theta's own I occurrences continue to use P, not the substituted operator argument. Calibration asserts equivalence, not that arbitrary P satisfies either schema.

No schema is inserted into a theory, and no actual least-set truth or ID1 derivation is claimed. For existing context-dependent least sets a later specialization must fix context pointwise; one cannot universally quantify contexts while pretending a single fixed P equals every context's least set. No proof before review/freeze, no register/transitivity/WF promotion.
