module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTransparentLambdaStep OriginalTransparentLambdaStepPrefixProof OriginalHereditaryLambdaGlobal
open OriginalHereditaryLambdaGlobalInternalProof (wrapperFactor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem wrapperIntroduction (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
    (s t cert parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) s)))
    (hold : Nonempty (Derivation body Delta (graph4 oldStep (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 (wrapper endpoint window oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hs := OriginalTransparentLambdaStepSpineProof.lambdaSpine s t cert parameter htag
  have hg := OriginalTransparentLambdaStepGuardProof.guards endpoint window s t cert parameter htag
  have hspine := conjunctionAccept oldStep
    (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) xs hold hs
  have hn := conjunctionAccept (OriginalSpineGuardLeaf.refined oldStep)
    (OriginalNeutralLeaf.leafGuard endpoint window) xs hspine (andLeft hg)
  exact conjunctionAccept (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))
    (InternalAcceptance.conjunction
      (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
      OriginalConstructorLeaf.variableGuard) xs hn (andRight hg)

/-- Whole same closed leaf, not merely its normalized raw factor. -/
theorem atWitnesses (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
 (rawIntroduction : OriginalGenericLambdaWrapperTargets.RawIntroduction source oldStep)
    (s t cert parameter childS childT childCert childParam d e context gamma extended
      arrow tail payload code state next : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended)))
    (hchild : Nonempty (Derivation body Delta
      (graph4 (closedLeaf endpoint window oldStep) (suc z) childS childT childCert childParam)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow arrow d e)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload childCert)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hs : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
    (hn : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert childParam))) :
    Nonempty (Derivation body Delta
      (graph4 (closedLeaf endpoint window oldStep) (suc z) s t cert parameter)) := by
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
  let normalized := oldStep
  let inner := wrapper endpoint window normalized
  have hchildHereditary := wrapperFactor endpoint window (OriginalHereditaryLambda.refined inner)
    childS childT childCert childParam hchild
  have hchildBoth := conjunctionRecover inner (OriginalHereditaryLambda.guard inner) ys hchildHereditary
  have hchildInner := andLeft hchildBoth
  have hchildGuard := andRight hchildBoth
  have hchildNormalized := wrapperFactor endpoint window normalized childS childT childCert childParam hchildInner
  have hparentNormalized := rawIntroduction body alpha Delta s t cert parameter
    childS childT childCert childParam d e context gamma extended h hchildNormalized
  have hparentInner := wrapperIntroduction endpoint window normalized s t cert parameter (andLeft hsf) hparentNormalized
  have hchildCheck := compositionValue inner OriginalTransparentLambdaStepFieldsProof.childPrograms
    (suc z) xs ![childS,childT,childCert,childParam] hchildInner hselectors
  have htransition := OriginalTransparentLambdaStepHereditaryControlProof.advance inner
    s t cert parameter arrow state next hs hm.1 (andLeft (andRight hsf)) (andLeft htf)
    hm.2 hlam hchildCheck hchildlive
  have hparentGuard := OriginalTransparentLambdaStepHereditaryRunProof.guardBackward inner xs ys
    code tail state next hpath hchildpath hs hn hc htransition hchildGuard
  have hparentHereditary := conjunctionAccept inner (OriginalHereditaryLambda.guard inner) xs hparentInner hparentGuard
  exact wrapperIntroduction endpoint window (OriginalHereditaryLambda.refined inner)
    s t cert parameter (andLeft hsf) hparentHereditary
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperCoreProof
