# Actual auxiliary substitution composition and beta environment

Draft requested 2026-11-04 13:06 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

The first two targets establish actual term and full-tuple substitution composition for theta:Gamma→Delta and eta:Delta→Theta. The composite maps each typed variable v to substitute(theta v)eta. The lambda case must prove equality of the actual lifted composite environments. Here is unchanged; there uses accepted substitution-through-weakening. This avoids assuming the composition theorem in its own binder proof.

The third target is the exact beta single-environment equation for body:sigma::Gamma and a:sigma in Gamma. Substituting the beta contractum by theta equals beta-contracting the lifted-substituted body against substitute a theta in Delta. Both sides reduce via genuine composition to environments on sigma::Gamma. Here agrees by definition; there agrees by accepted weakeningCancellation for theta(v). No variable availability or fresh-variable convention is needed.

These are literal typed syntax equalities preserving all heads, numbered labels, annotations, full argument types and occurrences. They are the beta algebra prerequisite for paper06 lambda-instance reasoning, not a theorem about the original ordinary ordering. No confinement, finite-window or precedence assumptions are needed for these equalities. No WindowStep compatibility, positive-count preservation, computability, ID1, all-term accessibility or original-order transitivity is claimed.
