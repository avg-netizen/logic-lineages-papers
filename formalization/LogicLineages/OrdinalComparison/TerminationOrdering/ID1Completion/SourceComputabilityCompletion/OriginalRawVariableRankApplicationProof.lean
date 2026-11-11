module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
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
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldApplicationProof

theorem rankApplicationForward (raw out domain first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (graph2 rankSum out first second)) := by
  apply binaryChildCases (fold .rank) z z first second _
  intro beta j Theta firstRank secondRank hj hfirst hsecond
  rw [graph2Rename]
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph3Rename] at hc'
  rw [graph1Rename] at ho'
  simp only [zRelabel] at hfirst hsecond
  have ha := applicationForward .rank (raw.relabel j) (out.relabel j) z z
    (domain.relabel j) (first.relabel j) (second.relabel j) firstRank secondRank hc' hfirst hsecond
    (rankToFold (out.relabel j) z z (raw.relabel j) ho')
  exact rankSumBackward (out.relabel j) (first.relabel j) (second.relabel j) firstRank secondRank
    (rankFromFold firstRank z z (first.relabel j) hfirst)
    (rankFromFold secondRank z z (second.relabel j) hsecond) ha

theorem rankApplicationBackward (raw out domain first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
    (ho : Nonempty (Derivation body Delta (graph2 rankSum out first second))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) := by
  apply binaryChildCases (fold .rank) z z first second _
  intro beta j Theta firstRank secondRank hj hfirst hsecond
  rw [graph1Rename]
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph3Rename] at hc'
  rw [graph2Rename] at ho'
  simp only [zRelabel] at hfirst hsecond
  have ha := rankSumForward (out.relabel j) (first.relabel j) (second.relabel j) firstRank secondRank
    (rankFromFold firstRank z z (first.relabel j) hfirst)
    (rankFromFold secondRank z z (second.relabel j) hsecond) ho'
  exact rankFromFold (out.relabel j) z z (raw.relabel j)
    (applicationBackward .rank (raw.relabel j) (out.relabel j) z z
      (domain.relabel j) (first.relabel j) (second.relabel j) firstRank secondRank hc' hfirst hsecond ha)


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
