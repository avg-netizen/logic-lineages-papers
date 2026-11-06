# Internal binder transport supplier

Baseline: `54e245c33ea9248d8de6fd5eb603e1c7a22b33d9`. Paper06 lem:id1
uses first-order induction invariants and universally quantified later
parameters (paper.tex lines 579–580, 590–596 and 606–613). The existing
InternalCalculus supplies actual finite proof trees, but its semantic
soundness/positivity results do not authorize syntactic binder transport.
This component supplies exact syntax equalities and one derived logical
rule required for future internal positive-body induction.

Targets retain original Formula.relabel, Formula.subst, allOne,
InternalCalculus.instantiate, liftPredicateFormula and Positive.relabel.
Their equalities are literal syntax, not equivalences of N-realization.
The internal universal transport target requires a closed DERIVATION of
phi -> psi and constructs a closed DERIVATION of forall phi -> forall psi.
It does not add a constructor, infer a proof from semantic truth, or assume
any source accessibility/computability closure. Positive-renaming equality
covers the entire existing positive grammar, including every binder.

Nonduplication: existing helpers establish semantic truth of relabeling,
substitution and quantifiers. No local theorem supplies these literal
transport equations or this derived internal universal implication rule.
Mathlib's low-level term/mapTermRel laws are reused where available.

Full internal body unfolding remains pending. Its intended next consumer
will require a separate structural positive-substitution derivation and
leastness argument. This component does not claim that consumer, source
closure, all-term computability, internal accessibility, whole lem:id1,
well-foundedness, or II5. No existing source/target, manuscript, register,
checker, dependencies, root imports or CI changes.
