# Weakening accessibility: exact conditional equivalence

Source: 06-godel-t-termination-ordering/paper.tex, fresh-variable use in the computability discussion (lines 590–597). This pays only accessibility transport, not the context stability of computability needed for a general fresh-variable argument.

The two targets give opposite implications between Acc of the reverse actual positive quotient path relation at the original confined representative and at its weakened representative. The edge convention is source x reduces to successor y; Lean Acc uses relation (y,x) := PositivePath H x y. Symbols, S, precedence and arity remain identical. SubtypeClosed and original packed source confinement are explicit. No membership assumption on the unused context type sigma is required.

Forward proof plan: induction on original Acc, generalized over confined packed representatives of its current number. For an arbitrary extended-context successor, accepted actualPositiveWeakeningReflection supplies a confined original r, its exact weakened representative equality, and the original positive path. Apply the induction hypothesis and rewrite that equality. No injectivity/global numeric map is needed.

Backward proof plan: a separate induction on extended-context Acc, generalized over confined original packed representatives whose weakened code is its current number. Given any original numeric successor, positiveClosure and liftPath provide a confined original r and exact endpoint representative equality. The accepted actualPositiveQuotientRenaming gives the extended positive path. Apply the induction hypothesis at r and rewrite its original representative equality. This uses forward renaming, not an inverse inferred from the first induction.

Both proofs retain arbitrary numeric successors. Their confined representative witnesses are derived, not assumed. No ambient well-foundedness, precedence transitivity, arbitrary-term accessibility, scalar least-set calibration, C stability, ID1 derivation or register change is claimed. The two implications together give the stated equivalence. No proof is authored before exact review and prospective freeze.
