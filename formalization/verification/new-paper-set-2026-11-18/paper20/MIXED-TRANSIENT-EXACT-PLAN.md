# Genuine mixed-selector pole/properness contraction plan

Scope before targets: current20 `lem:binary-transient`, all proper rational inputs with actual denominator A_d; then the separate complete profile theorem. No finite coefficient-vector state or assumed partial-fraction expansion replaces an actual rational input.

## Actual states and semantics

Use the accepted Basic canonical RatFunc C and literal embeddings X,C. Define step(true,f)=C(f), step(false,f)=C(X*f). The existing evenSelectorIdentity proves step(false,f) equals the actual canonical even rational square-root digit; true is definitionally the odd digit. Define proper(f) by f.num.degree < f.denom.degree, including zero. Define poleOrder(z,f)=f.denom.rootMultiplicity z, where f.denom is the actual reduced canonical denominator, not a supplied pole bound. Define low-bit-first execution on actual lists of Bool and actual RatFunc.

All field parameters remain arbitrary perfect characteristic-two fields, and all z in those fields are quantified. Geometric pole language is instantiated in an actual splitting/algebraically closed extension when needed, not inferred from roots in an unsplit base field alone. Full source specialization must explicitly account for this.

## Route avoiding a full partial-fraction theorem

We can prove local pole contraction for EVERY fraction without assuming partial-fraction coverage. For actual Q !=0, at each z factor Q=h^k*R with h=X-C(z), k=Q.rootMultiplicity z and R.eval z !=0. Mathlib `pow_mul_divByMonic_rootMultiplicity_eq` and `eval_divByMonic_pow_rootMultiplicity_ne_zero` pay this exact factorization.

For k=2j, write P/Q=(P*R)/(h^j*R)^2. For k=2j+1, write P/Q=(h*P*R)/(h^(j+1)*R)^2. Each identity is in actual RatFunc using genuine polynomial embeddings. For L0 use the same identities with numerator X*P. Actual square pullout and the accepted embedded-polynomial Cartier bridge then express the output with denominator h^ceil(k/2)*R. Its canonical reduced denominator divides that displayed denominator by RatFunc.denom_div_dvd. Since R(z)!=0, root multiplicity there is exactly ceil(k/2); divisibility proves the upper bound even with cancellations. This covers all numerators, including zero, rather than a selected finite sum of principal parts.

Separately the accepted both-digit same-denominator formula proves canonical output denominator divides original Q, hence no new poles anywhere. Contraction at canonical Q already implies this coordinatewise, but denominator divisibility is a stronger useful actual algebraic supplier.

## Properness without heavy RatFunc.intDegree imports

For canonical f=N/D proper, deg N < deg D. Both polynomial square-root digits of N*D have degree < deg D: any retained original coefficient index is at least twice the output index; deg(N*D)<2deg D. Prove this from actual coefficient extraction and polynomial degree facts, including the zero polynomial case. Both canonical rational digits have these numerators over D by the existing fraction update.

For any displayed fraction P/Q with deg P < deg Q, prove its reduced canonical fraction is proper by the actual cross-product identity f.num*Q=P*f.denom and polynomial degree addition. Cancellation cannot invalidate the inequality. This replaces—not assumes—the corresponding properness transfer. No intDegree, infinity-order oracle, or partial-fraction properness premise is needed.

## Source multiplicity budget and all words

Define literal A_d = product over i=1..d of (1+X^i) in the working field and prove equality with mapped F2 source polynomial when specializing. Define literal mu=sum 2^(padicValNat2 i), a=Nat.clog2 mu; no degree surrogate replaces mu. Prove A_d(0)=1 and hence nonzero.

Adapt (under distinct current names and provenance) the old genuine root budget proof: factor i=2^v*odd; separability of 1+X^odd gives multiplicity<=1, Frobenius expansion multiplies it by2^v, product root multiplicities sum. These are actual polynomial facts, not assumptions about roots. Avoid old BinaryDenominatorDefinitions import, which pulls matrix/series layers. The previous repeated-L1 pole-removal theorem is NOT imported as mixed closure.

Induct on actual binary words to retain properness and to bound each canonical pole order by ceil(initial order/2^length), using the proved one-step ceil(k/2). At length a and initial source multiplicity<=mu<=2^a, every output pole order<=1. Include empty denominator/product d=0, zero input, a=0 and all finite coordinates. A no-new-poles clause and properness at every prefix remain explicit; they are not inferred from the final simple-pole bound alone.

## Proposed staging and acceptance boundaries

1. Freeze exact actual fraction-properness transfer, polynomial-digit degree bound, both-step properness and denominator divisibility suppliers.
2. Freeze actual local denominator factorization/contraction for both selectors; no source A_d premise yet.
3. Freeze literal source multiplicity budget and actual-word iteration arithmetic.
4. Only then assemble complete source `lem:binary-transient`, with no assumed partial fractions or omitted coordinate/field extension issue.

The full residue-profile theorem still needs the independently defined simple-pole rational state space, complete partial-fraction bijection over all roots, Frobenius descent, both updates, actual output and all continuations. The contraction route above does not provide that global decomposition automatically. No profile or pure-L1 scalar-tail result may be substituted for it.

Resource feasibility remains untested. Use Basic-only RatFunc plus specific polynomial root/divisibility modules; every new frozen scope requires independent review and ordinary unchanged-cap native queue. No legacy source edits or cap changes.
