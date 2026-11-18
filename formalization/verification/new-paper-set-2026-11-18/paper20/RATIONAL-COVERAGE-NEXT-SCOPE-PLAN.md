# Next rational-coverage scope, after RootInterpolation6

Proposed staged packet, not yet frozen or accepted:

1. For each literal source splitting field K and complete root product T, define
   independent K-states by actual RatFunc canonical properness and f.denom ∣ T.
   This is not range(reconstruction). Zero is included; T is nonzero even when
   the root set is empty.
2. Prove every such state has an actual presentation E(U)/E(T), degree U<degree T.
   Use the canonical numerator/denominator and the actual polynomial quotient
   T/f.denom (or the unique divisibility witness), paying cross multiplication,
   nonzero denominators, degree cancellation and zero-f separately.
3. Conversely every U of degree below T gives proper E(U)/E(T), whose canonical
   denominator divides T by RatFunc.denom_div_dvd. These two directions are
   genuine independent-state coverage, not a premise assuming partial fractions.
4. For arbitrary tuples b on ALL roots, define N_b=sum C(b_z)*D_z and genuine
   PF(b)=sum rationalC(b_z)/(rationalX-rationalC(z)). Prove N_b(z)=b_z*D_z(z),
   degree N_b<degree T, and PF(b)=E(N_b)/E(T). The latter uses the literal omitted
   factor identity, all denominators nonzero and finite rational sum arithmetic.
5. Injectivity for arbitrary tuples follows by clearing T then evaluating at
   each root and cancelling D_z(z). Surjectivity to every independent state uses
   item2 and actual interpolation residues. No caller-supplied PF coverage.

This can yield a genuine K-state/ALL-tuple equivalence, but is not yet the source
F2-state/Frobenius-compatible-tuple equivalence. Descent must follow separately.

Geometric obligations remain explicit: denominator-divides-T must be proved
 equivalent to simple poles supported on the source roots after arbitrary
algebraic extension (or an algebraic closure). A K-root-membership condition
alone is invalid unless denominator splitting is also proved. A finite-field
irreducible factor with no K roots must not disappear from this condition.
For transient inputs, canonical denominators divide mapped A_d, giving genuine
splitting; the checked order<=1 bound must then imply divisibility by T.

Prefer a separate polynomial lemma for a nonzero SPLIT polynomial Q:
Q ∣ T iff every root lies in the complete source root set and every root
multiplicity is <=1. Then explicitly establish splitting for the intended
source states/inputs or prove algebraic-closure equivalence before promotion.
No complete-profile or executable conversion claim follows from this plan.
