# Complete auxiliary argument substitution laws

Draft requested 2026-11-04 13:10 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

Two exact structural equalities concern actual applyArguments and selfArguments from the Select/Copy rules. The first commutes typed substitution with full application of an argument tuple of arbitrary finite types, preserving arrows types tau, the same result type and the exact tuple order. It is not a unary approximation. The second commutes tuple substitution with the full selfArguments list, preserving label, head, extraTypes, requested types and every retyped numbered self-copy occurrence. Base and extras are substituted literally, without deleting or merging occurrences.

Both are finite recursion over the actual types/argument tuple, with arbitrary typed Gamma→Delta substitution. No window, confinement, precedence, injectivity or original-order transitivity assumptions are required for these syntax equalities. The Select occurrence transport is already separately available through argumentListSubstitute; these targets provide only its application/self-copy algebra. No WindowStep compatibility, positive count, computability, accessibility or ID1 claim is included.
