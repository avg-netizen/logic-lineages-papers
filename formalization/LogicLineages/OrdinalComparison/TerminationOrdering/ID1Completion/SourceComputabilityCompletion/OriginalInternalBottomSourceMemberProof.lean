module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceMemberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance OriginalUniverseDecoderInternalAcceptanceSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof
open OriginalUniverseDecoderInternalAcceptanceOutputProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem termMembership (H : Program 1) (M W : Program 2) (typ raw gamma c : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
 Nonempty (Derivation body Delta (graph2 M (numeral 1) typ c)) := by
 apply singletonCases 0 typ raw gamma _
 intro beta j Theta state work request hj hs hc hr
 simp only [graph2Rename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename]
 have ha' := renameInto ha j Theta hj
 rw [termAcceptedRename] at ha'
 apply outputCases H M W 0 state work request (gamma.relabel j) (typ.relabel j) (raw.relabel j) (c.relabel j) _ hs hc hr ha'
 intro xi k Xi out hk hguard _ _
 simp only [graph2Rename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename]
 have hr' := renameInto hr k Xi hk
 simp only [stepRequestRename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at hr'
 exact andLeft (OriginalUniverseDecoderInternalAcceptanceGuardRootProof.termRootForward M W
  (request.relabel k) ((gamma.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k)
  ((c.relabel j).relabel k) hr' hguard)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceMemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceMemberProof
