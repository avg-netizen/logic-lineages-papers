# Paper 16: actual symbolic J fold on the newly installed literal body

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
149–153 uses finite union internally on the original accepted multiset
carrier. This packet specializes the checked ordered parsed fold; it does
not build a proof tree by iterating over an externally supplied list.

* [Syntax](../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSparseJFoldSyntaxProof.lean):
  for the exact raw/scratch pair, the original full-language motive is
  `typedScratch_i(s) → (∀q scratchMember(s,q)→I(q)) → J(n)`.
  Both tags use the new exact `literalData i r` body, whose count observer
  is the actual literal permutation program, not the older opaque checker.
* [Support](../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSparseJFoldSupportProof.lean):
  an actual scratch member opens the original scalar premise, all-member
  evidence for the tail follows only through its literal scratch cons
  graph, and object equality transports J of the genuine raw term.
* [Fold](../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSparseJFoldProof.lean):
  a supplied genuine same-body J(empty) handles the nil raw equality.
  In a cons, exact actual typed-scratch cons gives the typed head and typed
  tail; actual head membership gives I(head), and the supplied same-body
  scalar-to-singleton rule gives J of its exact raw singleton. Apply the
  actual strict-tail induction result to its typed scratch and true
  transported scalar membership predicate. The literal actual observer
  and same-tail parser construct U for the exact raw cons, and the checked
  same-body conditional union composes the two original J proofs. The
  conclusion is transported to the exact original raw input.
* The premises are `LiteralEmptyMembership`, `LiteralScalarSingletonPromotion`,
  explicit `CertifiedOriginSplit` on this exact same body, and the actual
  positive parse/typed scratch/universal scalar member reports. Neither
  empty nor singleton membership is manufactured by this artifact. No
  count observer property is assumed: the literal U and typed union
  carrier are checked imported suppliers. Unconditional J closure and
  numbered arithmetic accessibility are not claimed.

Native status: source only; one named exact axiom audit.
