# Complete effective equal-gap certificate assembly

Source target: prop:equal-gap, compute a threshold and decide eventual identity or one fixed strict order for fixed equal-gap intervals. This assembly is intended for numbered credit only after the full fresh conjunction passes and independent final review confirms source completeness.

## Literal program and explicit tail

On raw codes mu,nu,delta, let E=originalLeadingCode(delta). If initialPassCode is true, return pureCertificateCode(mu,nu,E). Otherwise return numericalComparison(rawProfileCode nu E,rawProfileCode mu E). Thus the result is a concrete0/1/2 sign, independent of the eventual input t and of f within its chosen threshold B.

Set initial radius R0=20+rawNorm(delta)+rawNorm(mu)+rawNorm(nu). Use the literal tail max(thickBlockTail R0 B,pureCertificateTailCode(mu,nu,E,B)). No monotonicity of thickBlockTail is presumed: each existing gate is paid by its own explicit max component. All raw inputs have total primitive-recursive sign and tail programs, and the sign always lies in0..2.

## Complete actual correctness scope

Normal mu,nu,delta; offsets zero-or-limit; delta positive limit; selected f/B. For every t on the computed tail and arbitrary actual states A,A' below epsilon zero with common actual norm t and limit parts mu+delta,nu+delta, produce genuine first entries and actual norm-orbit identities. The numerical comparison of those actual entry norms equals the literal fixed program sign. This is stronger than the source canonical countInitial inputs and must not assume equal finite tails, phase visits or hits.

Additionally expose the source tail trichotomy: the computed sign0 gives strict < for every admitted tail input, sign1 gives equality for every admitted tail input, and sign2 gives strict >. State this on canonical countInitial intervals as a wrapper if needed to remove any ambiguity about source entry maps; prove their affordability and actual normalization rather than supplying it.

## Proof

Derive original leading normal code and its repr=log(delta), and E>=1 from positive-limit delta. Obtain original actual hits/orbits from entry existence using R0 and t. Exact InitialPassCode iff selects checked ActualInitialPeeling.

Failure produces an actual original-clock relative-limit divergence with exact leading-cost sign. Both relative limits retain omega^E. Derive common current norm by actual nonfinite orbit laws and offset affordability by selected growth. Checked ActualDivergenceEntryOrder gives strict final order, with both orientations covered and equality excluded by actual divergence sign.

Pass gives genuine simultaneous first hits at mu+omega^E,nu+omega^E with original norm clock. The second max tail component remains valid at the larger common norm. Invoke full PureCertificate on the actual reset states and the actual normal leading code. Compose genuine first hits using target gap>=omega, identify them with original actual hits, and transport actual norm comparison without asserting equal finite tails.

No full arithmetic/threshold-inverse/collision/theorem credit beyond prop:equal-gap follows. Source future cocycle/field comparison dependencies remain separate.
