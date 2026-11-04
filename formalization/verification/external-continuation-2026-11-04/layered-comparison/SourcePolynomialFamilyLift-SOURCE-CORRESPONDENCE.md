# Simultaneous admissible polynomial fields

Paper09 hardness.tex lines 188–193 lifts the nonzero polynomial unknowns in a chosen zero pattern to positive admissible first fields. This component combines the accepted unary norm-padding extension finitely, without changing the source syntax or admissibility model.

For p:Fin n→(Nat→₀Nat), with every p i nonzero, SimultaneousExtension extends any genuine substitution on Γ to List.replicate n unary ++ Γ. prefixVariable is literal head-first Fin.cases indexing; oldVariable inserts exactly n unary names via Variable.there. Each new head has full signedCNF matching its polynomial, is positive below omega^omega, and its scalar is exactly N(head)+1. Every old typed coordinate is preserved literally. The n=0 case is included.

SignedInputCalibration specializes to the unchanged SignedPair.Context n, inputVariable and inputs, so the polynomial indices have the actual compiler's order, not a renamed or reordered surrogate. It gives the simultaneous full-CNF and padding facts at those exact inputs.

Zero coefficients within a nonzero polynomial are allowed. A zero polynomial as an entire unknown is excluded by the explicit premise; later zero-pattern substitution must handle that case separately. No primitive-recursive extraction from existence, source encoding, simultaneous equation reduction, polynomial-system undecidability or whole functional-hardness claim is made. No manuscript/register/export changes.
