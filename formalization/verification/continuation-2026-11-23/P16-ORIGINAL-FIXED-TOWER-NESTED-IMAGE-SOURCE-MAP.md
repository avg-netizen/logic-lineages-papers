# Paper 16: exact fixed-tower nested image reflection and well-order

Paper 16 ordinals.tex (B_T) and (D) give the exact native higher-type
inner map and the concrete tower term at every level. The independently
checked fixed-tower nested families use those identical terms and fit
every finite positive dimension below the *same* tower for each fixed
l (receipt 1795454198264175250-14). This packet proves the converse
comparison and identifies their induced image orders.

* `NativeTowerNestedInnerOrbitReflectionProof` proves actual lex
  trichotomy at every dimension; equality and an opposite comparison
  contradict the original closed native strict well-foundedness.
  The resulting comparison equivalence and injectivity are for the
  exact same nested points and exact original `NativeBelow`.
  The root uses only Lean core externals.
* `NativeTowerNestedInnerOrbitImageRelIsoProof` transports the lex
  well-order to the actual subtype of literal native image terms,
  using the product lex theorem and `Equiv.ofInjective`; the forward
  native term and the physical bound on **every image point** are
  stated explicitly. It imports only the two lightweight exact
  Mathlib relation/equivalence modules, not the Ordinal library.

No claim compares two distinct dimensions or asserts that the cuts
`j ↦ evaluatedInner l j` are inflationary, that the union is a single
well-order of named ordinal type, or that rank/height has been calculated.
