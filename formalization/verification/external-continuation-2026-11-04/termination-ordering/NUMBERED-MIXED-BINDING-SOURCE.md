# Exact mixed renaming/substitution naturality

Draft requested 2026-11-04 12:55 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

Four targets concern actual auxiliary terms and complete typed argument tuples. First, substituting after renaming equals substitution by the pointwise composite environment. Second, renaming after substitution equals substitution by the pointwise renamed environment. Both have term and tuple versions, with the exact Gamma→Delta→Theta directions shown in the targets. All native annotations, labels and tuple occurrences remain literal; typed maps need not be injective or confined.

The first binder equation compares liftSubstitution theta after a lifted renaming with liftSubstitution of their pointwise composite, by here/there cases. The second compares a lifted substitution followed by a lifted renaming with the lift of the renamed environment. Its there branch uses the accepted auxiliary renaming-composition equality and exact equality of weakening/renaming composites. No substitution-after-substitution theorem is assumed, and no binder equation is replaced by a type-erased code equality.

These are binder-algebra prerequisites for the lambda-instance reasoning of paper06 lines591–597 and eventual openNumbered/beta compatibility. They are not substitution composition, positive reduction compatibility, count preservation, computability, original-order transitivity, ID1 or all-term claims. Actual substitution composition and the beta single-environment equation remain separate obligations.
