# Actual primary-equivalence substitution

Draft requested 2026-11-04 12:36 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

Source correspondence is the actual fixed-window primary equivalence used in paper06's quotient and lambda-instance reasoning (lines591–597). This is not substitution stability of the obstructed original ordinary ordering and not positive reduction compatibility.

Two targets preserve WindowPrimary on actual packed endpoints and WindowArgumentPrimary on actual typed tuples under arbitrary actual typed Substitution Gamma Delta. The packed map keeps the exact result type and applies the existing auxiliary substitution to the term. The same symbols and S are retained. Under a lambda, the proof must use actual liftSubstitution rho into sigma::Delta; no context weakening or variable availability is assumed globally.

The ordinary and numbered head-exchange generators keep their original head/window/type guards. Their base permutation must be transported by mapping every actual packed occurrence through substitutePacked. Substitution may identify distinct occurrences, but does not delete multiplicity, change labels or alter the ordering of extras. The tuple relation transports its head and tail recursively. Both function-side and argument-side equivalence contexts are retained, without adding any positive argument reduction.

No confinement premise is required to preserve this raw equivalence relation. A later finite-carrier result would separately need GoodSubstitution/range confinement and accepted universe preservation. No WindowStep substitution theorem, preservation of positive step count, beta composition equation, computability, ID1, original-order transitivity or all-term result is included.
