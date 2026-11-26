# Complete residue-profile observer: concrete proof architecture

Goal: exactly current20 `thm:residue-observer`, not an old pure-Cartier cycle theorem or a state vector defined to have desired behavior. The new accepted binary transient is an input supplier only; it does not prove a profile bijection.

## 1. Actual finite splitting field and ALL roots

For d>=1 take K_d=(SourceBudget.denominator (ZMod2) d).SplittingField. Pinned Mathlib SplittingField.Construction provides actual splitting and finite-dimensionality and a `Finite` instance over a finite base. Obtain actual field/Algebra F2/CharP2/PerfectRing2 and a finite root set S_d from the distinct roots of the mapped full A_d, not a handpicked orbit. Prove exact membership iff A_d(z)=0, nonzero roots from A_d(0)=1, and Frobenius stability. Squaring gives an injective self-map of the finite set, hence a permutation. No root set or fixed-field property is supplied as an oracle.

Use the complete squarefree product T_K=product over z in S_d of (X-C(z)), with T_K monic, degree card(S_d), distinct/simple roots and nonzero constant. Prove its coefficient Frobenius image is itself by reindexing the whole root set. Fixed coefficients satisfy x²=x, hence x=0 or1 (field factorization x*(x-1)=0). This explicitly proves that fixed elements are exactly the embedded F2, without assuming a fixed-field classification. Construct the unique descended T_2 polynomial coefficientwise, prove T_2.map=T_K, and identify it as the source squarefree part. This includes every root and every cancellation possibility.

## 2. Independent rational state space, not range(PF)

Define base states directly as f:RatFunc(ZMod2) with canonical properness and, after the actual rationalMap into K_d, canonical denominator dividing T_K. Prove that this is equivalent to the source condition 'simple poles only in all roots S_d': the denominator is nonzero, splits over K_d because its roots are contained in a split source denominator / it divides T_K; conversely use polynomial root multiplicities and factorization to show divisibility. Avoid circular definitions: do not define states as partial-fraction sums or as profile outputs.

One useful independent alternative is f.num.degree<f.denom.degree and f.denom divides T_2. Prove equivalence to the geometric version via actual scalar-extension degree/coprimeness/denominator facts, not assume it. Choose the version whose equivalence proof is feasible under the unchanged cap. Cancellation and zero f are included. If arbitrary rational denominators are quantified geometrically, demonstrate the denominator splits from the all-roots condition in the actual splitting/algebraically closed setting rather than relying on base-field root absence.

## 3. Concrete complete partial fractions via root products

For each z define D_z=product over S_d.erase z of(X-C(y)); prove T_K=(X-C(z))*D_z and D_z(z)!=0. For any U with degree<U bound card S_d, define b_z=U(z)/D_z(z). Prove the polynomial identity

U = sum_z C(b_z)*D_z.

Evaluate at each root: all terms except z vanish and the surviving denominator is nonzero. Degree of both sides is <card S_d, so equality follows from the actual root-count/evaluation uniqueness theorem (or pinned Lagrange.eq_interpolate). This is a constructive finite polynomial proof of coverage, not an assumed partial-fraction theorem. Injectivity follows by the same evaluations for arbitrary tuples.

Divide that polynomial identity by T_K in actual RatFunc to obtain PF(b)=sum_z C(b_z)/(X-C(z)). Conversely any independent state has denominator dividing T_K; multiply its actual numerator by the quotient to produce U with deg U<deg T_K, paying the degree inequality and every denominator nonzero condition. Then apply the identity. This covers EVERY proper fraction, not only a preselected finite principal-part sum. Empty-root/d=0 extension, if retained, is treated separately with only the zero state; full source still uses d>=1.

Pinned Mathlib Lagrange has degree_interpolate_lt, eval_interpolate_at_node and eq_interpolate, but also imports Vandermonde. Prefer a direct finite root-product degree/evaluation proof if importing the full package breaches caps.

## 4. Frobenius compatibility and actual F2 descent

Profiles are the subtype of ALL functions b:S_d->K_d satisfying b(z²)=b(z)². The tuple space is finite because K_d and S_d are finite; compatibility is an actual equation, not a promise of reconstructibility.

Prove coefficient-Frobenius naturality of PF by actual rationalMap and reindexing roots. The image profile obeys b'(z²)=b(z)². Injectivity of PF then proves that an actual base F2 rational state's profile is compatible. Prove base F2 extension is fixed under coefficient Frobenius using actual map composition / finite F2 coefficient arithmetic.

Conversely for compatible b define N_b=sum C(b_z)*D_z. Reindexing gives Frobenius-fixed N_b; T_K is already fixed. Descend BOTH polynomials coefficientwise to F2 and prove that their genuine rational fraction maps to PF(b). Pay degree/properness and state membership. This avoids the unsupported leap 'rational Frobenius invariant implies coefficients lie in F2' by constructing the base fraction. Uniqueness uses injectivity of rationalMap and complete partial-fraction uniqueness. Final deliverable is an actual Equiv between the independently defined base state subtype and compatible profiles.

## 5. Both literal transitions and output

Define T1(b)_z=sqrt(b_z), T0(b)_z=sqrt(z*b_z). Prove each preserves compatibility using actual Frobenius/sqrt identities and the root permutation; derive F2 linearity if retaining the source proof's stronger assertion. Lift these to actual profile endomaps.

Prove actual RatFunc intertwining step(i,PF(b))=PF(T_i(b)). Use the checked rational Cartier additivity (and a finite-sum lemma), all-root sums, and actual simple-pole local laws for both branches. L0's constant summand must be killed, not discarded by definition. Existing Basic local rules genuinely pay this, and naturality transports it to the base state. No partial coordinate family may replace the complete tuple.

Define scalar out_K(b)=sum_z b_z/z, then prove it is Frobenius fixed using compatibility and reindexing, and construct its unique actual F2 value. Independently identify this with coefficient0 of the genuine regular rational expansion of the reconstructed base state. A root-product calculation N_b(0)/T_K(0)=sum b_z/z (char2, all roots nonzero) plus accepted presentation independence can pay this. Do not define output as the actual answer and separately assert the sum without proof.

## 6. Every continuation after the ACTUAL transient

Use checked FullTransient to put every proper U/A_d after every prefix of length a into the independent simple-state space. This still requires proving its canonical denominator divides T_K from no-new-pole/support and simple multiplicities; do not silently assume it.

Define profile execution on arbitrary Bool lists in the same low-bit-first order. Prove by induction that reconstruction equals the actual rational execution for EVERY remaining word; the output equality must also hold for every such continuation. Tie both rational selectors to genuine power-series binary selection: true already has the odd coefficient bridge; false uses C(X*f) to derive the even coefficient rule, with square roots fixing actual F2 coefficients. No all-ones-only orbit substitutes for arbitrary words.

## 7. Acceptance and explicit scope boundaries

Stage reviewed frozen packets: actual source finite field/root/Frobenius facts; root-product interpolation/coverage; independently defined state equivalence and descent; both transitions/output; all-word and transient assembly. Each must keep actual definitions, source maps, unchanged caps, named axiom audits and recursive evidence. Original accepted Basic/transient suppliers remain immutable; no legacy broad import edits.

The source's prose exact cardinality 2^(degree squarefree A_d) is a useful subsequent consequence, but cannot be claimed from mere finiteness. Effective field construction/factorization and executable initial-profile conversion are likewise distinct from noncomputable SplittingField existence; report this scope explicitly if not formalized. The numbered theorem's actual finite space/bijection/maps/output/all-continuation claims must all be assembled before promotion. No completed profile theorem is claimed by this plan.

## Critical geometric-state guard

In step2, the predicate 'every K_d-root of the denominator lies in S_d' alone is NOT the source state condition: an unrelated irreducible denominator may have no K_d-roots. The geometric condition must explicitly quantify poles in an algebraic closure, or explicitly include denominator splitting in K_d and prove that this is equivalent to having all geometric poles in S_d. Defining states by denominator divisibility is independent and sound, but its equivalence to the printed geometric phrase must pay this nonvacuity issue. Do not infer splitting from a base-field root-membership implication alone.
