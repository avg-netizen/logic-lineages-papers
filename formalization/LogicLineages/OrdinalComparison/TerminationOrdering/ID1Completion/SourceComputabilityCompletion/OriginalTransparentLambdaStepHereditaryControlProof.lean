module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryControlProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNeApply)
open OriginalHereditaryLambda OriginalHereditaryLambdaChildStateProof
open OriginalHereditaryLambdaChildControlProof (nonzeroBranchIntro liveNonzero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A matching lambda target is not the literal same-type bottom. -/
theorem sameBottomReject (s t cert parameter typ : OTerm alpha)
    (htype : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) t))) :
    Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.sameBottom (suc z) s t cert parameter).not) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  let P := graph4 OriginalLambdaGuardLeaf.sameBottom (suc z) s t cert parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb := OriginalConstructorLeafInternalProof.sameKnownLeftRecover (.projection 1)
    OriginalConstructorLeaf.expectedBottom t xs hp (projectionValue 1 xs)
  have htypeAt := unaryValue InternalUnpair.left (.projection 0) typ s xs (withHyp htype P) (projectionValue 0 xs)
  have hc := unaryRecover BottomRepresentative.bottomCode (leftOf (.projection 0)) t typ xs hb htypeAt
  have hthree := BottomSourceValidityProof.bottomConstructorTag t typ hc
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (suc z) (numeral 3)
    (Fin.cons t Fin.elim0) (withHyp htag P) hthree
  exact ⟨Derivation.implicationIntroduction (numeralNeApply 1 3 (by decide) he)⟩

theorem stopZero (s t cert parameter typ : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.sourceLambda (suc z) s t cert parameter)))
    (htype : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) t))) :
    Nonempty (Derivation body Delta (graph4 stop z s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  exact successorBranchIntro _ _ _ z z xs
    (normalizeAccept OriginalLambdaGuardLeaf.sourceLambda xs hs)
    (normalizeReject OriginalLambdaGuardLeaf.sameBottom xs (sameBottomReject s t cert parameter typ htype htag))

/-- The original hereditary transition, unlike the new normalizer, checks
actual child acceptance. That acceptance is extracted from the same refined
child, never assumed at the parent. -/
theorem advance (oldStep : Program 4) (s t cert parameter typ state next : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state s t cert parameter)))
    (hs : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.sourceLambda (suc z) s t cert parameter)))
    (htype : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) t)))
    (hm : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.matchingTarget (suc z) s t cert parameter)))
    (hp : Nonempty (Derivation body Delta (graph4 lamPath (suc z) s t cert parameter)))
    (hc : Nonempty (Derivation body Delta (graph4 (OriginalLambdaGuardLeaf.childCheck oldStep) (suc z) s t cert parameter)))
    (hn : Nonempty (Derivation body Delta (graph4 childLive next s t cert parameter))) :
    Nonempty (Derivation body Delta (graph1 (transition oldStep) next state)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  let us : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hstop := atLiveValue stop z state s t cert parameter hl (stopZero s t cert parameter typ hs htype htag)
  have hadvance := conjunctionAccept OriginalLambdaGuardLeaf.matchingTarget _ xs hm
    (conjunctionAccept lamPath (OriginalLambdaGuardLeaf.childCheck oldStep) xs hp hc)
  have hguard := atLiveValue (advanceGuard oldStep) (suc z) state s t cert parameter hl hadvance
  have hnext := atLiveValue childLive next state s t cert parameter hl hn
  have hactive : Nonempty (Derivation body Delta
      (graph1 (OriginalHereditaryLambdaChildControlProof.activeBranch oldStep) next state)) := successorBranchIntro _ _ _ next z us (normalizeAccept _ us hguard) hnext
  have hbranch : Nonempty (Derivation body Delta
      (graph1 (InternalAcceptance.branch
        (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (atState stop))
        (OriginalHereditaryLambdaChildControlProof.activeBranch oldStep) (.projection 0)) next state)) := zeroBranchIntro _ _ _ next us
    (normalizeReject (atState stop) us (OriginalTransparentLambdaStepGuardProof.rejectAtZero _ us hstop)) hactive
  exact nonzeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1) _ next state us
    (projectionValue 0 us) (liveNonzero state s t cert parameter hl) hbranch
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryControlProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryControlProof
