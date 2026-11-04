# Exact weakening and numbered opening substitution

Draft requested 2026-11-04 13:00 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

These three syntax targets pay the binder algebra for the actual Abs/openNumbered rule, a prerequisite for paper06 lambda-instance reasoning (lines591–597). The term and full-tuple laws commute substitution through weakening: weaken into sigma::Gamma, then substitute by liftSubstitution theta, equals substitute by theta and weaken into sigma::Delta. They follow from the two accepted mixed naturality directions and literal lifted-there behavior, not substitution composition.

The opening law sends substitute(openNumbered label f sigma tau base extraTypes extras)(liftSubstitution theta) to openNumbered with exactly the same label, head, sigma, tau and extraTypes, and pointwise substituted base/extras. The complete actual suffix extraTypes++[sigma] remains intact. The appended fresh binder is exactly here; its image under lifted substitution is the same here. Accepted substituteAppend and the tuple weakening law pay the equalities.

All quantification is over arbitrary actual typed syntax and Gamma→Delta substitution. No finite-window confinement, ordering or injectivity assumptions are needed for these equalities. This is not beta/substitution composition, actual WindowStep compatibility, preservation of positive counts, computability, ID1 or original-order transitivity.
