# Next numbered result: scalar repeated-Cartier corollary

Source: current20 sections/cartier.tex, cor:scalar-profile, lines181–207.
This is separate from accepted full thm:residue-observer (packet095).

## Exact obligation

For d>=1 and every actual proper F2 source fraction P/A_d, define beta_z as
the INITIAL simple coefficient in its genuine full partial-fraction expansion
over the actual source splitting field. For every ell>=Nat.clog 2 mu(d),
the actual base canonical series constant of C^[ell](P/A_d), embedded into K,
equals the sum over ALL actual source roots of inverseFrobenius^[ell](beta_z)/z.
No supplied expansion, root subfamily, or post-transient residue definition may
replace the initial beta. Degree condition includes zero numerator. Suppressed
poles have zero coefficients. No new effectivity/cardinality/trace/kernel claim.

## Reuse and real gap

Accepted Basic local rules and finite additivity, SourceBudget root bounds,
SplittingRoots completeness, canonical extension, regular selectors and true
series output are reusable. The existing RationalCoverage theorem only covers
simple states AFTER the transient; it does not establish the initial beta.
Legacy CartierProper/Local targets provide properness/local rules, not full
higher-pole coverage. They add no missing mathematical supplier and importing
that old broad stack risks already documented resource limits.

Pinned Mathlib Algebra/Polynomial/PartialFractions.lean has actual existence
and uniqueness for pairwise-coprime monic polynomial powers in an actual
polynomial algebra with actual inverses. Its imports are modest (algebra basic,
polynomial division, coprime lemmas); target-only cap preflight still required.
Names: mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse and
quo_add_sum_rem_mul_pow_inverse_unique. No polynomial-part zero premise is
provided by these results; that obligation must be proved here.

## Staged implementation before full comparator

1. Genuine bounded principal-parts supplier. Over K=FieldAt d let T be the
   accepted full-root product and M=mu(d). Prove actual mapped A_d divides T^M
   from actual splitting, full root support and checked multiplicity bound.
   This uniform denominator avoids choosing unverified pole vectors. For any
   proper source P/A, construct its actual bounded numerator over T^M and prove
   degree<U denominator degree. Apply Mathlib to factors X-z, powers M and
   actual inverse embeddings. Degree<1 remainders are constants; clear real
   denominators and compare degrees to prove polynomial part is zero. Prove
   uniqueness including zero/empty cases. Define beta from unique coefficients
   at exponent1, not from later iterates. Supporting-only packet first.

2. Actual one-pole repeated-C theorem. For any k>=1 and coefficient b, prove
   the actual rational iterate of b/(X-z)^k. Simple k=1 gives inverseFrob^ell b.
   For higher k, a surviving iteration requires k-1 divisible by 2^ell, with
   surviving order 1+(k-1)/2^ell. Thus 1<k<=M<=2^ell forces disappearance.
   Pay finite-sum iteration using actual C additivity and the local odd/even
   integer-power rules. This is stronger than generic contraction alone:
   contraction allows order1, but repeated odd Cartier never reaches1 from k>1.

3. Assemble full scalar comparator. SourceBudget supplies M<=2^ell for every
   ell>=a. Actual naturality transports the base iterate. All higher initial
   terms vanish; remaining actual rational state is the true reconstruct of
   inverseFrob^ell beta. Use already checked actual rational/series output and
   base regularity, not a formal output oracle. Exact source comparator freezes
   before assembly proof and final review. No promotion from stages1 or2 alone.

## Resource and scope boundaries

Independent scope review precedes each target/proof. First native action would
be parent-granted target/import preflight under the existing unchanged checker
and caps; no legacy edits or upstream build. Principal-parts existence/uniqueness
and q=0 are substantial new obligations, not bookkeeping. Mathematical choice
for unique coefficients does not establish executable conversion. The trace
paragraph, linked numeric parameter bound, subsequent cycle results and source
algorithmic prose are not part of this numbered corollary's acceptance.
