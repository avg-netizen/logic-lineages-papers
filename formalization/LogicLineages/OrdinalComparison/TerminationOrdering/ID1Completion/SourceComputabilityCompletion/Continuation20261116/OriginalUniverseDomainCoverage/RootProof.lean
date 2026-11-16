module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.RootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalAcceptanceCheckerProof (singletonCases)
open OriginalUniverseDecoderInternalAcceptanceOutputProof (outputCases)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open OriginalTypedDecoderInternalRequestSyntaxProof (stepRequestRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalLambdaConstructorGraphSyntaxProof (andLeft)

theorem requestedType (H : Program 1) (M W : Program 2) (typ raw gamma context : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma context))) :
    Nonempty (Derivation body Delta (graph2 M (numeral 1) typ context)) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Theta state work request hj hs hc hr
  simp only [graph2Rename,numeralRename]
  have haj := renameInto ha j Theta hj
  rw [termAcceptedRename] at haj
  have hprogram : OriginalUniverseDecoderInternalFuelSingletonSupportProof.checkFor H M W 0 =
      OriginalUniverseDecoder.termCheck H M W := by
    unfold OriginalUniverseDecoderInternalFuelSingletonSupportProof.checkFor OriginalUniverseDecoder.termCheck
    congr 1
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  have hcheck : Nonempty (Derivation body Theta
      (programGraph (OriginalUniverseDecoderInternalFuelSingletonSupportProof.checkFor H M W 0)
        (numeral 1) ![typ.relabel j,raw.relabel j,gamma.relabel j,context.relabel j])) := by
    rw [hprogram]
    exact haj
  apply outputCases H M W 0 state work request (gamma.relabel j) (typ.relabel j)
    (raw.relabel j) (context.relabel j) _ hs hc hr hcheck
  intro beta' k Xi out hk hg hstep hout
  simp only [graph2Rename,numeralRename]
  have hrk := renameInto hr k Xi hk
  simp only [stepRequestRename,numeralRename] at hrk
  exact andLeft (OriginalUniverseDecoderInternalAcceptanceGuardRootProof.termRootForward M W
    (request.relabel k) ((gamma.relabel j).relabel k) ((typ.relabel j).relabel k)
    ((raw.relabel j).relabel k) ((context.relabel j).relabel k) hrk hg)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.RootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.RootProof
