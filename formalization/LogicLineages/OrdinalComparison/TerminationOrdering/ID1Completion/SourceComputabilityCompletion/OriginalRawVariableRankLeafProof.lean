module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableActionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
open OriginalRawSyntaxTransportInternalVariableActionProof

theorem rankVariableForward (raw out index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (equal out (numeral 1))) :=
  variableActionSpecForward .rank out z z index
    (variableForward .rank raw out z z index hc (rankToFold out z z raw ho))

theorem rankVariableBackward (raw out index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (ho : Nonempty (Derivation body Delta (equal out (numeral 1)))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) :=
  rankFromFold out z z raw (variableBackward .rank raw out z z index hc
    (variableActionSpecBackward .rank out z z index ho))

theorem rankBottomForward (raw out tau : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw tau)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (equal out (numeral 0))) :=
  bottomForward .rank raw out z z tau hc (rankToFold out z z raw ho)

theorem rankBottomBackward (raw out tau : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw tau)))
    (ho : Nonempty (Derivation body Delta (equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) :=
  rankFromFold out z z raw (bottomBackward .rank raw out z z tau hc ho)

theorem rankNilForward (raw out  : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (equal out (numeral 0))) :=
  nilForward .rank raw out z z hc (rankToFold out z z raw ho)

theorem rankNilBackward (raw out  : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation body Delta (equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) :=
  rankFromFold out z z raw (nilBackward .rank raw out z z hc ho)


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
