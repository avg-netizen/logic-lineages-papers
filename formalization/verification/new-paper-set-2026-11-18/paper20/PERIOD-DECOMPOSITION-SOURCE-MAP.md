# Single exact actual rational decomposition interface

Four pins. Body is identical to accepted Basic.Targets.ActualRationalSquareRootDecomposition,
with Basic names opened in a distinct namespace. Arbitrary perfect char2 fields
and ALL actual RatFunc inputs, including zero. No supplied denominator, inverse,
valuation or decomposition premise. Same canonical num/den digits and embeddings.

Purpose: genuine smaller proof import closure for the all-integer Hahn law.
Proof will import BasicPolynomialProof and use actual polynomial decomposition
plus fraction identities, not BasicRationalProof, FieldSimp or Ring. All original
period/Laurent target pins remain unchanged. Local polynomial lift formula in
generic proof will be proved via IsFractionRing.lift_algebraMap and actual
translated polynomial injection, with no TranslatedRationalProof import.
No period/transport acceptance from this single supporting identity.
