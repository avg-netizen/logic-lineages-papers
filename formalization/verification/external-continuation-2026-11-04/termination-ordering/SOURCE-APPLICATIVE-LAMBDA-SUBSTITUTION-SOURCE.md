# Conditional computable substitution for an applicative-body lambda

Source paper06 lines582–597 and620–622, a restricted lambda case of structural computable substitution. The source is a literal lambda with body generated only by variables, bottom and application. Nested lambda, ordinary and numbered constructors in that body are excluded. Substitution images may contain arbitrary constructors under the explicit assumptions.

Both scalar bodies are explicitly calibrated against the same successfully decoded Context, one at Delta and the other at sigma::Delta. SubtypeClosed is explicit. The actual typed theta has separately guarded GoodSubstitution, old-context pointwise computability, and explicitly supplied fresh-context computability of every weakened image. The theorem does not derive the last premise from the old one. Source lambda confinement supplies sigma membership, arrow membership and body confinement.

Accepted FreshEnvironment gives Good/C for lift theta. Restricted applicative substitution at sigma::Delta yields C of the substituted body in the fresh least-set interpretation. Accepted C-to-accessibility and exact encodedR calibration give literal body quotient Acc required by ConditionalLambda. Original theta's actualSubstitution gives confinement of the substituted lambda.

For every confined computable old-context argument a, ArgumentEnvironment gives Good/C of extend theta a. The same restricted body theorem at Delta proves C of that substituted body. ExtendedBetaIdentity identifies it with the actual beta instance of substitute body (lift theta). ConditionalLambda then gives the displayed lambda computability in the old interpretation. Fresh and old predicates are not equated; only literal quotient body Acc crosses between the two uses.

No general context computability weakening, arbitrary lambda-body theorem, full language substitution preservation, precedence assumption, ID1 derivation or global WF. No proof before exact review/freeze; no export.
