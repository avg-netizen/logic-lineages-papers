module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTransparentLambdaStep OriginalTransparentLambdaStepPrefixProof OriginalTransparentLambdaStepRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem transitionAtLive (source : Program 2)
    (s t cert parameter state next : OTerm alpha)
    (hl : Nonempty (Derivation body Delta
      (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
    (hg : Nonempty (Derivation body Delta (graph4 (hopGuard source) (suc z) s t cert parameter)))
    (hc : Nonempty (Derivation body Delta
      (graph4 OriginalHereditaryLambda.childLive next s t cert parameter))) :
    Nonempty (Derivation body Delta (graph1 (OriginalTransparentMixedPathDefinitions.transition source) next state)) := by
  have hguard := OriginalHereditaryLambdaChildStateProof.atLiveValue
    (hopGuard source) (suc z) state s t cert parameter hl hg
  have hchild := OriginalHereditaryLambdaChildStateProof.atLiveValue
    OriginalHereditaryLambda.childLive next state s t cert parameter hl hc
  exact successorBranchIntro _ _ _ next z (Fin.cons state Fin.elim0)
    (normalizeAccept _ (Fin.cons state Fin.elim0) hguard) hchild

theorem atWitnesses (source : Program 2)
    (s t cert parameter childS childT childCert childParam d e context gamma extended
      arrow tail payload code state next : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow arrow d e)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload childCert)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hs : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
    (hn : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert childParam))) :
    Nonempty (Derivation body Delta (graph1 (OriginalTransparentMixedPathDefinitions.transition source) next state)) := by
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
  exact transitionAtLive source s t cert parameter state next hs hguard hchildlive

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaCoreProof
