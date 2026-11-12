module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHopProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTransparentLambdaStep OriginalTransparentLambdaStepPrefixProof OriginalTransparentLambdaStepRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The six extra witnesses are only outputs of already-total arithmetic
Programs; the public theorem below eliminates them internally. -/
theorem atWitnesses (source : Program 2) (oldStep : Program 4)
    (s t cert parameter childS childT childCert childParam d e context gamma extended out
      arrow tail payload code state next : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow arrow d e)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload childCert)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hs : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
    (hn : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert childParam))) :
    Nonempty (Derivation body Delta
      ((graph4 (refined source oldStep) out s t cert parameter).iff
        (graph4 (refined source oldStep) out childS childT childCert childParam))) := by
  have hsource := andLeft h
  have hsc := andLeft (andRight h)
  have htc := andLeft (andRight (andRight h))
  have hst := andLeft (andRight (andRight (andRight h)))
  have htt := andLeft (andRight (andRight (andRight (andRight h))))
  have hprefix := andLeft (andRight (andRight (andRight (andRight (andRight h)))))
  have hparam := andLeft (andRight (andRight (andRight (andRight (andRight (andRight h))))))
  have hext := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
  have hchildparam := andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
  have hsf := OriginalLambdaConstructorGraphFieldsProof.constructorFields s d e childS arrow hsc hst ha
  have htf := OriginalLambdaConstructorGraphFieldsProof.constructorFields t d e childT arrow htc htt ha
  have hm := OriginalTransparentLambdaStepFieldsProof.matching s t cert parameter childS childT d e arrow hsf htf
  have hp := parentPair cert childCert code tail payload hprefix hl hr hc
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  let ys : Fin 4 → OTerm alpha := Fin.cons childS (Fin.cons childT (Fin.cons childCert (Fin.cons childParam Fin.elim0)))
  have hpath := unaryValue InternalUnpair.left (.projection 2) code cert xs
    (pairLeft cert code payload hp) (projectionValue 2 xs)
  have hchildpath := unaryValue InternalUnpair.left (.projection 2) tail childCert ys hl (projectionValue 2 ys)
  have hlam := lambdaPath xs code tail hpath hc
  have hsourceAt := binaryValue source (.projection 0) (.projection 3) (suc z) s parameter xs
    hsource (projectionValue 0 xs) (projectionValue 3 xs)
  have hguard := conjunctionAccept (OriginalTransparentVariableStep.sourceAt source) _ xs hsourceAt
    (conjunctionAccept OriginalLambdaGuardLeaf.sourceLambda _ xs hm.1
      (conjunctionAccept OriginalLambdaGuardLeaf.matchingTarget OriginalHereditaryLambda.lamPath xs hm.2 hlam))
  have hstrip := stripPrefix cert childCert code tail payload hprefix hl hr hc
  have hselectors := OriginalTransparentLambdaStepFieldsProof.selectors s t cert parameter
    childS childT childCert childParam d e arrow context gamma extended hsf htf hstrip hparam hext hchildparam
  have hchildlive := compositionValue OriginalHereditaryLambda.live
    OriginalTransparentLambdaStepFieldsProof.childPrograms next xs ![childS,childT,childCert,childParam] hn hselectors
  have htransition := transitionAtLive source s t cert parameter state next hs hguard hchildlive
  let P := graph4 (refined source oldStep) out s t cert parameter
  let Q := graph4 (refined source oldStep) out childS childT childCert childParam
  obtain ⟨hf⟩ := refinedForward source oldStep xs ys code tail state next out
    (withHyp hpath P) (withHyp hchildpath P) (withHyp hs P) (withHyp hn P)
    (withHyp hc P) (withHyp htransition P)
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := refinedBackward source oldStep xs ys code tail state next out
    (withHyp hpath Q) (withHyp hchildpath Q) (withHyp hs Q) (withHyp hn Q)
    (withHyp hc Q) (withHyp htransition Q)
    (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHopProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHopProof
