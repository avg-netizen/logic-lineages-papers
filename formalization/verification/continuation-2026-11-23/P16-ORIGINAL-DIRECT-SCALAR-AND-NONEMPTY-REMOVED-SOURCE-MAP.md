# P16: original direct source/target scalar guards and nonempty removal

Source-only freeze. Gate ScratchNumericProof (exact_TypedScratchFromOriginalMap,
exact_NumericPresentScratch), then RawNumericProof (exact_NumericRawGuards),
then independent NonemptyProof (exact_OpenRemovedScratchNonzero,
exact_OpenRemovedScratchCons) and OpenProof (exact_OpenRawGuards).
Static import checks found no Hydra, GameAdd, full Sym2, or Rank.

## Original exact boundary

* `NumberedWindowDirectAlgorithm.directLists` has both complete decoded
  source and target lists tested by the same scalar, and a separate
  `!removed.isEmpty` conjunct (ordinals.tex 74–105). The three raw inputs
  here are source, target, removed (the removed raw field from the
  witness, not the opaque witness code). The #1501–1502 actual shared
  three-parser program keeps all three literal original sparse unpack
  results and fails a malformed input instead of supplying an empty list.
* No duplicate list fold. Map one existing exact-one normalizer
  `conjunction scalar (constantOne 1)` through the original physical
  `InternalListMap.map`; run the existing original scratch membership
  on that exact ordered mapped list at literal zero. Its zero branch
  returns one. All numeric correctness is at the original arbitrary
  `ScalarFit scalar accepts` (exact output 0/1 on every numeral), with
  the two actual ordered `List.all accepts` values. Nil accepts here;
  duplicates are never discarded and no order assumption is supplied.
* Removal nonemptiness is on the actual parsed **scratch code**, not
  the parser tag. Valid raw nil really parses successfully to zero
  scratch and fails removal. The accept-at-zero contradiction in
  original ID₁ gives `(eqn decodedRemoval z).not`; actual total
  original head and tail plus `reconstructNonzero` produce one
  actual first removed cell. Neither a numeric witness nor a
  caller-supplied scratch membership is used.
* The combined raw object CPS returns the actual three positive parser
  reports, two held actual scalar-fold reports on the same decoded
  source/target, and the actual cons of that same removed payload.
  Scalar fit is a numerical hypothesis only. This packet does not
  yet turn an arbitrary physical scalar-fold report into a proof of
  scalar acceptance at a chosen member (a separate map/member
  transport), and it does not equate old opaque d with this checker.

No permutation, map of inserted targets, full direct checker, J
accessibility, numbered promotion, or mutation of old sources.

## SHA-256 source pins
```
88049146da1311327ee3ab56eb9d8c70df332319c2bba8af1cad6d4dd0190725  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectBoundaryGuardsTargets.lean  (local closure: 1042)
dd7c3bb32bcc8e1f148ceb382d4a622b635cc6250557629b2081ed8e69cd5b1f  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectBoundaryScratchNumericProof.lean  (local closure: 1097)
249dd0f76a3bfafeb8cb8376a07b00a2f6f34b4aeae5a44fbcda5cbe7f1215b6  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectBoundaryRawNumericProof.lean  (local closure: 1111)
3c2c11cd24f29fcc73db62a371c2bc809cd7a6adf0f6b0621bd54ba04652e520  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectBoundaryNonemptyProof.lean  (local closure: 1102)
21905aa9513a01ff13ecc7a21c6d703026e16d0cc9ad15fc5ad112935955dcd0  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectBoundaryOpenProof.lean  (local closure: 1104)
```

Unchanged original sources:
```
781ec264d98428a9068e59190f5fbac631bc3bc46470c024f13bf05b206e6e33  formalization/LogicLineages/PersistentMarking/NumberedWindowDirectAlgorithm.lean
3eeebf432fe2136f2a828c5fb1f896ea26e06facc13e3688911a7c520ccae314  formalization/LogicLineages/PersistentMarking/NumberedWindowDirectProgramProof.lean
132aa95648e74180aa6507215169ccd6e916f3dd0d352c69d6c09983f2c9fc85  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectSourcePartitionRawTargets.lean
42ef4c0c527ce2ca12d02a31450242bb1db87e9044627a764ed25c92605cab0e  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectSourcePartitionRawGraphProof.lean
64519ff9b4e099a3e055a87af1f2a718f60e2f073fb2f432e9ecbcbbd79c3e81  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectSourcePartitionRawProof.lean
557c0499b52372d7296e1d6030221540c6b08b77387746299efc395a3f25fe3b  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalSparseFieldParserNumericChecks.lean
61c5b39141606e7bb4b041ac26a06cd5e2f0da084416c9c433848259f89876fa  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalSparseScratchMembershipNumericProof.lean
1b8d16fecbccfb79daed08bb04e45dacfacb2c10656a4a47e5e221937236729e  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalFreshProbeDispatchProgramControlProof.lean
ef2564b06c5730b7824367e4b245a4e0b5aaa5682e8f9c2b914c5ff4f9a43aa9  formalization/LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalListMapDefinitions.lean
0ffd4dec887c4cffa27ea5190914221d9e2e1a5022df226b2bb56a53dbd1b614  formalization/LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalListMapEvaluationProof.lean
74c99b418c35fcdc824cc6281f7bd15b70d71f6f878ce2c1e43d0167f5be9824  formalization/LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalListCodecDecompositionSupportProof.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
```
