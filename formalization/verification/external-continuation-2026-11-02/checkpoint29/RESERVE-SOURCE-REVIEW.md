# Paper09 reserve: source-clause review supplement

This is a separate review supplement; no accepted frozen correspondence or comparator has changed.

## Domain (source lines 69–81, 128–138)

“Annotated scalar” is used in the section's generated-source context: original scalar assignments and their retained scalar copies, ground closures and ground scalar partials. It does **not** mean every arbitrary ordinal expression equipped solely with the Lean predicate `ActiveScalarAnnotation.Annotated`. That predicate deliberately records only operator provenance and head-active implies tail-active, not all grades or the additive-head invariant. The latter is the independently proved `AdditiveHeadTree.ScalarTrees` certificate. Consequently `ScalarCarrierAccounting.ExactAccounting` exposes BOTH certificates honestly; it does not claim `Annotated` alone implies the theorem.

For every member of the complete printed grammar, without an extra hypothesis, `AdditiveHeadTree.Proof.actualSourceTrees` and `ActiveScalarAnnotation.Proof.actualSourceAnnotation` construct these certificates for its actual full assignment. Their assignment vectors are identified by `Option.some.inj`, not assumed equal. This is assembled in `ScalarCarrierAccounting.actualSourceAccounting` and `AccountSemanticDeterminacy.actualSourceSoundness`.

The retained derived scalars remain covered: `scalar_expand/scalar_repeated` and `annotated_expand/annotated_repeated` preserve certificates under literal copies/sums; `headClosureScalar` and `headClosureTransport` preserve them under actual ground closure; `groundPartialTrees` and `groundPartialTransport` preserve them under a successful actual ground scalar partial. Partial success is derived from generated grade in the actual transport assembly, never postulated for an arbitrary expression. `SelectedAccountPreparation.certificateRenaming` and the proved selected permutation handle any finite prefix of ground binders. Derived scalars are not asserted to be original source terms.

## Literal accounting and identity (lines 128–152)

`ScalarCarrierAccounting.Account` has exactly the free/tracked, active add, finite head, nonfinite head clauses. The list retains order and duplicate occurrences, a stronger representation than a multiset. Every element is an actual unary source plus its complete actual assignment and a proof of no free ground names. `carrierSum` is ordinal natural sum; `c : Nat` is finite/nonnegative; the final `+ c` is ordinary finite ordinal addition. `reserve xs c = (c : Int) - 3 * xs.length` is integer arithmetic only.

`exactAccounting` constructs the actual successful F-scalar partial and literal identity for every remaining ground valuation. `accountingOrigin` proves actual selected-head provenance of each occurrence. `AccountSemanticDeterminacy.universalSoundness` extends the identity to EVERY Account. Determinacy asserts ordered head values, c, length and reserve, NOT syntactic equality of actual source labels. Thus existence choices do not create incompatible semantic witnesses.

## Ground units (lines 154–155)

`GroundCarrierTransport.exactAccountTransport` keeps the EXACT same actual label objects, ordered occurrence list and c, hence the same d. The lifted map fixes tracked F and maps old names below it. Literal source zero maps to ordinal one. `actualSourceGroundTransport` proves whole actual assignment and actual partial naturality and their common-unit identity; it does not assert numeric invariance of arbitrary ground-dependent scalar values.

## Ground scalar partials at every nested binder (lines 155–159)

`GroundPartialCarrierTransport.groundPartialAccount` quantifies arbitrary left/right typed contexts and the actual selected F. From both source-built certificates and an Account it derives ground run success and an Account of the derivative scalar with the EXACT same actual carrier list and c′ ≥ c, hence d′ ≥ d. `actualSourceGroundPartial` includes original and permuted complete assignments and both actual selected-F partial identities. The adjacent swap kernel is generalized by actual typed permutation naturality, not claimed to cover prefixes by fiat. Certifying the derivative does not identify it with a new source.

## Source lower bounds (lines 160–175)

`SourceReserveLowerBound.renamedSourceLowerBound` proves the bound for EVERY Account of the scalar of EVERY unchanged generated source under any injective typed renaming sending F to here. `actualSourceLowerBound` discharges assignment/existence hypotheses and retains the original complete vector. `sourceFloor` is 1 on inactive sources and bare F, 4 on active applications, and 5 on active ground lambdas. Ground/free constructors are inactive; a ground-typed active source cannot be bare F. No source is excluded to obtain the bound.

`positiveHeadValue` proves actual generated positive heads have common-unit value ≥ 1. The finite application branch pays this positivity; the nonfinite branch pays surplus ≥ 1 and explicitly excludes a bare-F operator by its unit head 1. The ground argument branch pays its own non-bare source bound.

The lambda proof uses the actual abstraction's FULL vector size sum: factor = 2 * sum_i partialSize(h_i), not the scalar size alone. It proves factor ≥ 2, transports actual accounts through the ground partial and closure, and constructs repeated accounts with literal occurrence list `(List.replicate factor xs).flatten`. The final sum gives reserve ≥ 5. All arbitrary ground-prefix/context changes are proved through injective lifted renaming and swap.

## Boundary

These claims cover the source-context reading of annotated scalars and all operations explicitly used in the printed reserve proof. They do not promote a theorem for arbitrary ungraded `Annotated` expressions, assert actual-label uniqueness, or establish the later one-final-abstraction, original-budget construction or decision claims.

## Reviewed completion

The complete source-context clauses of paper 09 `lem:reserve` were reviewed against the manuscript and accepted after the checkpoint 29 exact 148-alias aggregate and its independent source/axiom audit. This is a source-clause mapping, not a new compilation or a theorem for arbitrary ungraded annotated expressions. The historical scoped checkpoint summary is preserved. The public target register remains unchanged pending authorization; this completed source result is not yet registered. No full-root or CI pass is claimed.
