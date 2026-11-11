module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalBranchProof (orCases)
open OriginalUniverseDecoderInternalAcceptance OriginalUniverseDecoderInternalAcceptanceLeafSupportProof
open OriginalUniverseDecoderInternalAcceptanceCouplingGuardProof
open OriginalUniverseDecoderInternalFuelInclusionStepProof
open OriginalUniverseDecoderInternalGuardProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Acceptance of the actual guarded output rules out the rejection arm and
recovers the literal original typed transition, not a native step oracle. -/
theorem acceptedTypedTransition (H : Program 1) (M W : Program 2) (state out c : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (graph2 (OriginalUniverseDecoder.transition H M W) out state c)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma (graph1 (OriginalTypedDecoder.transition H) out state)) := by
  apply orCases (stepRefinement H M W out state c ht)
  · have hz : Nonempty (Derivation body (equal out z :: Gamma) (equal out z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hbot⟩ := acceptedRejectImpossible H M W out c hz (withHyp ha _)
    exact ⟨Derivation.explosion hbot⟩
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem acceptedRequestGuard (H : Program 1) (M W : Program 2)
    (state work request suffix out c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request suffix)))
    (ht : Nonempty (Derivation body Gamma (graph2 (OriginalUniverseDecoder.transition H M W) out state c)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) request c)) := by
  let C := OriginalUniverseDecoderStepSpecification.guardSpec M W (numeral 1) request c
  apply formulaCases C
  · exact guardBackward M W (numeral 1) request c
      (show Nonempty (Derivation body (C :: Gamma) C) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  · have hn : Nonempty (Derivation body (C.not :: Gamma) C.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := transitionRejectedGuard H M W state work request suffix c (withHyp hs _) (withHyp hc _) hn
    have he := valueUnique (OriginalUniverseDecoder.transition H M W) out z ![state,c] (withHyp ht _) hz
    obtain ⟨hbot⟩ := acceptedRejectImpossible H M W out c (by simpa only [equalEqn] using he) (withHyp ha _)
    exact ⟨Derivation.explosion hbot⟩

theorem guardedTransition (H : Program 1) (M W : Program 2)
    (state work request suffix out c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request suffix)))
    (hg : Nonempty (Derivation body Gamma (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) request c)))
    (ht : Nonempty (Derivation body Gamma (graph1 (OriginalTypedDecoder.transition H) out state))) :
    Nonempty (Derivation body Gamma (graph2 (OriginalUniverseDecoder.transition H M W) out state c)) :=
  transitionAcceptedGuard H M W state work request suffix out c hs hc
    (guardForward M W (numeral 1) request c hg) ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchProof
