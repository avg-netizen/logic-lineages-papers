# Exact primary lambda-body inversion

Draft for review, no proof/export.

Source correspondence: actual WindowPrimary lam congruence and equivalence closure, supporting paper 06 lambda reasoning at lines 590–597. Existing PrimaryShapes proves only lambda shape and application components. This target exposes the actual body relation in the identical extended context sigma::Gamma, with identical result type tau, for arbitrary packed target q.

The iff states primary equivalence of packed lam body and q exactly when q is packed lam body' at the original arrow type and the bodies are WindowPrimary in sigma::Gamma. It is generic in Symbol, arity, symbol/type windows, with no finite-carrier, subtype-closure or reduction assumptions. The relation is actual WindowPrimary, not erasure equality or a step.

Potential proof uses a dependent lambda view retaining binder type and packed body; relation-preserving equivalence induction handles refl/symm/trans/lam. Outer type preservation enforces identical binder/result types. One-H beta-application decomposition, substitution-environment congruence and lambda computability remain separate. No export or ID1 conclusion.
