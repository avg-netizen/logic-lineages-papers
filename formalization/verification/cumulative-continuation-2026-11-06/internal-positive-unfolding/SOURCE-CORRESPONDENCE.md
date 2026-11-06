# Internal unfolding of the original positive body

Baseline: `37994f3f9de5974fef2d0ec66cc22d61c3308938`. Paper06 lem:id1
introduces the one tagged positive definition and uses its closure and
induction schemas (paper.tex lines 564–572 and subsequent I/J inductions).
This component derives an actual finite internal proof of unfolding for the
EXISTING Positive grammar and EXISTING InternalCalculus, then instantiates
it with the original SourcePresentation.sourceBody. No rules are added.

The structural contraction target states that replacing I by body(I) in any
positive formula p entails p, INTERNALLY. Its atomic case must use the
original inductiveClosure rule, while conjunction, arithmetic guards and
universal binders use actual logical derivations. The binder supplier is
reused syntactically, not as a semantic truth assumption.

The exact closure step for the invariant body(I) is then constructed, with
only its literal replacedBody assumption. Existing leastness yields the
reverse direction I -> body(I). Original closure supplies body(I) -> I.
The full target is an empty-context Derivation of the biimplication at any
literal term, retaining ordinary parameters. The final source instance names
the original tagged sourceBody directly, with its actual Program structure.

Nonduplication: the existing standardUnfolding theorem is only a standard-N
least-model equivalence. The earlier internal induction theorem REQUIRES a
closure-step derivation and does not construct this one. The new target
requires the actual syntactic derivations, with no model, accessibility,
source computability closure, derivability or extra axiom premise.

This proves the fixed-point law of the positive body, NOT the substantially
stronger closure of C_tau, constructor/lambda/substitution induction, or
all-term accessibility. The whole paper06 lem:id1 remains pending. No II5,
well-foundedness overclaim, existing source/target/rule, manuscript, register,
checker, dependency, root import or CI change. Comparator-first and exact
standard-axiom/source matching requirements remain unchanged.
