# Bounded frontier decision for plain-Phi existential closure

The program iterates an explicit finite state: a Bool recording successful finite
cases and a list of literal successor formulas. Each actual split preserves the
state's existential meaning and strictly decreases every successor's distinct
nonlinear-name count. The original name-occurrence length plus one is a concrete
fuel bound, so no search oracle or unbounded recursion is introduced.

The required decision contract is existential closure of an arbitrary Boolean
matrix in the literal plain-Phi row language. None rejects hyperPhi syntax;
inside the fragment, both truth and falsity must match existence of an original
natural valuation. This does not assert parameterized QE, alternating quantifier
prefixes, hyperPhi quantified coverage or full nonlinear BASE decision. Numeric
encoding/effectivity of the entire frontier iteration remains a separate gate.
