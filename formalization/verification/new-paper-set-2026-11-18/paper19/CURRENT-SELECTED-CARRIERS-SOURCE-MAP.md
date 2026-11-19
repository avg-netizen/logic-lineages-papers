# Paper19 lem:carriers: actual selected unary carrier, current policy/control

Numbered source is `sections/realization.tex` 56–71. The actual tracked
grammar, common-unit valuation and retained source/scalar annotation are
in lines 1–26; ground coordinate and generated positive support are in
`sections/setting.tex`. Each selected nonfinite head is backed by the
actual annotated operator, then by a unary original source with that
very unit first field; literal source-zero closure eliminates ground
captures but never replaces its scalar with an invented one.

* The frozen first premise is the direct actual-source
  `TrackedSource.Generated` grammar, with all positions of a single
  tracked free typed variable F, all result arities and internally
  arbitrary typed opaque blocks with real source occurrence exclusion.
  Its existing `TrackedSource.Proof.exactGrammar` covers the corresponding
  intrinsic syntax with erasure. `ActiveScalarAnnotation.Proof.actualSourceAnnotation`
  derives the current selected-policy annotation, and the genuinely
  p-parametric `SelectedHeadCarrier.Proof.operatorExtraction` gets
  the actual full operator assignment. No annotation, array of carriers,
  default policy, or witness to an all-one source is supplied as input.
* The new literal `renameTrackedAt F` is global and typed. It places
  the fresh same-type J in front of the same source context, sends F to
  J, and sends every other variable to its unchanged weakened identity.
  The old tracked slot remains unused. The target ranges over an arbitrary
  original typed position, not just the context head; nested binders are
  handled by the unchanged actual `Term.rename` and its lifted renaming.
* `carrierAt` applies exactly r literal zero arguments to the globally
  renamed actual operator of arity r+1 and then uses actual
  `UnaryCarrier.closeGround` (source substitution which maps every free
  ground reference to literal 0, leaving other functional names). The
  retained unary field and scalar remain in the same actual selected-policy
  assignment. `GroundSaturation` asks even for literal first-field
  preservation, because with a ground argument the positive box is the
  same indexed operator field, with no optional scalar-tail association.
* `Realization` records the actual operator vector, actual saturated
  renamed unary vector, and actual ground-closed unary vector. It includes
  the exact `GroundClosing.vector` equality, its scalar coordinate with
  no reset, no free ground occurrence and no residual occurrence of old
  F after fresh renaming. The same actual common units (all remaining
  functional coordinates one, original shared ground raw coordinates
  wire+1) interpret both head values. Finite ground valuations need not
  agree because generated positive-field support independently excludes
  every ground variable. The original f is arbitrary; only the actual
  `ParametricSourceSuccessor.denoteWith f` is used.
* The endpoint covers **every** selected head, which supplies the
  printed nonfinite subcase without ever conflating a selected inactive
  head with an occurrence discarded by the grammar; there is no carrier
  accounting/multiset/budget assertion in this lemma. A selected head is
  a literal occurrence relation that descends in active scalar branches,
  never into its positive syntax.

Reuse old source-choice-free raw syntax and p-parametric annotation,
selected-operator extraction, generated positive support, renaming and
ground-closing naturality as genuine suppliers. The old complete
`UnaryCarrier.Proof.actualCarrier` and `SelectedHeadCarrier.Proof.actualSelectedCarriers`
are default-only and cannot discharge the current target. The new proof
must independently pay fresh positional scope, literal ground application
and the actual arbitrary f denotation, then whole numbered theorem.
No existing source edited. Require independent exact target scope and
target-only preflight before any proof. Exact final statement and complete
recursive native artifacts/evidence require a distinct reviewed gate.
