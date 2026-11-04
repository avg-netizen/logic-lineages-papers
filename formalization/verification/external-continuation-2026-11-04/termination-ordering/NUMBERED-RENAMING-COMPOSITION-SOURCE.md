# Literal auxiliary renaming composition

Draft requested 2026-11-04 12:46 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

The two targets concern existing intrinsically typed auxiliary syntax and its actual renaming functions, a binder-algebra prerequisite for the lambda-instance reasoning in paper06 lines591–597. Renaming Gamma→Delta followed by Delta→Theta must equal the single pointwise composite on actual terms and typed argument tuples.

The lambda case must use actual Renaming.lift on each map, preserve the newly bound here variable and prove the there branch agrees with the lifted composite. Base/extras argument tuples preserve their complete type lists, order and multiplicity; numbered labels, heads, output types and native annotations remain literal. Renamings need not be injective.

No fresh variable is manufactured, no context is assumed inhabited, and no confinement, finite-window, precedence or original-order transitivity hypothesis is needed. This is not a substitution composition/naturality theorem or a reduction compatibility theorem. It supplies a prerequisite for those later proofs, without any step, computability, accessibility, ID1 or all-term claim.
