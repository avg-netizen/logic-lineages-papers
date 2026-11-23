# Paper 16 (T): original free/bottom C at any arrow into ground

Original source: `16-persistent-marking-termination-ordering/sections/ordinals.tex:113–127`.
These are two source-only supporting gates, pending exact native checking.
Neither changes the selected relation defining the ambient ID₁ body
`sourceBody (literalNeutral i r) c`.

1. `NumberedWindowInternalLiteralNeutralGroundEndpointProof`:
   hold actual `accepts (outputGuard i (refinedApplication p)) f u y`
   and a real free or bottom equality for f. The first physical projection
   retains the original shape-refined input tape and the actual selected
   `RawDomain i y`; the original DomainRules convert the latter into
   the actual even scalar carrier of **the same** `literalNeutral i r`.
   The original shape decoder peels its four held fields. On the actual
   declaration equality `ty = numeral (typeCode (.arrow σ .ground))`,
   real object cons injectivity gives both `dom = numeral (typeCode σ)`
   and `cod = numeral (typeCode .ground)`. The continuation keeps all
   fields, original packed argument and aux output equations, and the
   same actual y carrier. It does not identify distinct a/a′, reflect
   evaluations, or claim full h-typing of y.
2. `NumberedWindowInternalLiteralNeutralArrowGroundCProof`: actual
   application introduction in the original type formula, with its two
   universal eigenvariables, genuine new physical application premise
   and the full `Cσ` premise in context. The auxiliary I result needs
   only actual ground output shape and scalar carrier, so it does not
   need to consume Cσ. For bottom that auxiliary I is already paid by
   `exact_OpenLiteralNeutralBottomAuxI` on the **same body**. Free
   has exactly one named open supplier, `FreeAuxiliaryI`, the shape +
   scalar ⇒ auxiliary I rule of the same body, not a generic C assumption.

σ is any original source type, including non-ground. This is a curried
**one-application** result into ground, not arbitrary higher codomains
or universal C→I. It does not choose h, reuse old h-dependent forms,
prove existence of a typed fresh report, or transfer any result to a
different ambient relation. Numeric calibration of the new p for fixed
S/K belongs to the separate output-guard packet; this symbolic
conclusion makes no inference from numerical equivalence.

Serial roots: EndpointProof (1515 local / 30 external), then ArrowGroundCProof
(1517 / 30). No Hydra, Linarith, Rank, GameAdd or Sym2 in the scanned import closure.

Exact current source and premise pins (SHA256):
~~~text
aa8b0d148bd30ce40253d16f1b529a253a09247af56c0513827420b5bcfa8473  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralNeutralGroundEndpointProof.lean
e2c0c5b726a9e4ef0be348be6d8ce31e8f24386178a6110fc66f35ac7190f101  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralNeutralArrowGroundCProof.lean
23657cae1ae92150b5e5deb4ee565fe0ae34f7f0be5dbfb304a900e90b0193de  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof.lean
1ff3104fa1db45158b69a4f3737888c095b78f4aa5b5b8465fd68e3c98dd8dcb  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalTypedNeutralEndpointCasesProof.lean
27d48c026115a4d9275818e9a5e380ea35a107381bbc5dc3d9e27f2ce11467dc  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardOpenProof.lean
0175d05246e5b3d462df6523daf29eca64f38ddc6a19847870a915b02eba5a14  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAtomicApplicationShapeObjectChecks.lean
5de4ccc5e0fd50d3c9f3723bd985277229a92aa76c4a79aab8100d9e3bc90b6f  formalization/LogicLineages/PersistentMarking/NumberedWindowTypeApplicationRuleChecks.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
~~~
