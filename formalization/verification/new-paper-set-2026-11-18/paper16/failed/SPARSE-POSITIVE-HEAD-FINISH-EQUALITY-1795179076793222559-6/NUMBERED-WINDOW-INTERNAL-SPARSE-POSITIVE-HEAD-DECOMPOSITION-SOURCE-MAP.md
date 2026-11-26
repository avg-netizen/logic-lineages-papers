# Original sparse positive fold: actual first successful head and remaining finish

Scope: two exact supporting object derivations for the same
chosen `positive raw least` compiler program at arbitrary original
free terms. No code re-selection, old sourceBody transport,
raw/least callback semantic correctness, or matching theorem.

- `ordinals.tex:70–76,115–127` retains actual finite positive
  numerical certificates on quotient classes. Neither external
  finite path semantics nor numeral-wise proof enumeration is an
  internal derivation rule.
- `NumberedWindowPositivePathAlgorithm.lean:25–44` and
  `...InternalSparsePositiveFold.lean:49–68`: the chosen actual
  finish takes encoded current, starts at S(source), keeps the
  actual raw certificate and uses that raw certificate as fuel.
  The final literal positive AST accepts exactly when the raw
  certificate is nonzero and the actual finished current is
  S(target). `OpenPositiveFinish` uses exactly this true finish
  graph, no assumed terminal premise.
- `...InternalSparseFieldInductionTargets.consGraph` and
  `...InternalSparsePathAdvanceTargets.selectedGraph`:
  `headData` uses genuine original polynomial cons at cert
  and actual advance at [ctx,type,S(source),raw head]; the
  output is actual S(nextClass), never encoded none0. Remaining
  finish starts at S(nextClass), same context/type, unchanged
  raw tail as its own fuel, and returns actual S(target).
- `OpenPositiveHeadDecomposition` uses the retained original
  `InternalFiniteBlocks.block` with three object variables in
  order [head,tail,nextClass]. It gives both implications, not
  data already supplied as premises. Tail 0 is allowed and need
  not be positive; for a valid one-hop witness, remaining finish
  is exactly the actual nil case.

Proof plan after unchanged target preflight:

1. Actual walked finish graph, original nonempty branch,
   equalityTest and conjunction acceptance support (#654/#658)
   supply `OpenPositiveFinish` both ways. Directly choosing
   a genuine walk result by graph totality is permissible;
   alternatively the checked open scratch characterization
   (#661) and actual finish branch (#655) pay the result.
2. Given actual positive, its finish is successful and cert is
   nonzero. A leading gap would force this same finish to be
   zero by #664, contradicting genuine successor versus zero
   in the original object arithmetic. Eliminate actual
   sparse-cons existential to obtain raw head and tail, and
   select actual advance result by original graph totality.
3. Actual own-code fold recurrence (#663) gives the same
   successful tail finish at that encoded advance result. It
   cannot be zero by #664 no-current result and actual graph
   functionality. The genuine arithmetic zero/successor case
   supplies an actual next class; transport the advance output
   and tail's encoded-current input, then introduce the exact
   three retained binders.
4. Conversely these genuine witnesses give nonzero cert by
   original polynomial-cons arithmetic (#616) and recover
   whole finish via #663, so actual positive follows.
   Malformed, empty, and missing-head outcomes are never
   silently treated as a successful encoded class.
