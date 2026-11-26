module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
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
open OriginalRawSyntaxTransportInternalFoldNumberedProof

theorem rankNumberedForward (raw out label head tau base types extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (graph2 rankSum out base extras)) := by
  apply binaryChildCases (fold .rank) z z base extras _
  intro beta j Theta firstRank secondRank hj hfirst hsecond
  rw [graph2Rename]
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [programRename,OriginalRawSyntaxTransportInternalCancellationNumberedProof.tupleSixRename] at hc'
  rw [graph1Rename] at ho'
  simp only [zRelabel] at hfirst hsecond
  have ha := numberedForward .rank (raw.relabel j) (out.relabel j) z z
    (label.relabel j) (head.relabel j) (tau.relabel j) (base.relabel j) (types.relabel j) (extras.relabel j) firstRank secondRank hc' hfirst hsecond
    (rankToFold (out.relabel j) z z (raw.relabel j) ho')
  exact rankSumBackward (out.relabel j) (base.relabel j) (extras.relabel j) firstRank secondRank
    (rankFromFold firstRank z z (base.relabel j) hfirst)
    (rankFromFold secondRank z z (extras.relabel j) hsecond) ha

theorem rankNumberedBackward (raw out label head tau base types extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (ho : Nonempty (Derivation body Delta (graph2 rankSum out base extras))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) := by
  apply binaryChildCases (fold .rank) z z base extras _
  intro beta j Theta firstRank secondRank hj hfirst hsecond
  rw [graph1Rename]
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [programRename,OriginalRawSyntaxTransportInternalCancellationNumberedProof.tupleSixRename] at hc'
  rw [graph2Rename] at ho'
  simp only [zRelabel] at hfirst hsecond
  have ha := rankSumForward (out.relabel j) (base.relabel j) (extras.relabel j) firstRank secondRank
    (rankFromFold firstRank z z (base.relabel j) hfirst)
    (rankFromFold secondRank z z (extras.relabel j) hsecond) ho'
  exact rankFromFold (out.relabel j) z z (raw.relabel j)
    (numberedBackward .rank (raw.relabel j) (out.relabel j) z z
      (label.relabel j) (head.relabel j) (tau.relabel j) (base.relabel j) (types.relabel j) (extras.relabel j) firstRank secondRank hc' hfirst hsecond ha)


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
