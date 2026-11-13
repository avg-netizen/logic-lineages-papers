module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionSelectorContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open InternalTagArithmeticSupportProof
open OriginalContextInsertion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atLength (forwardRow deletionPrefix childCount deletionCount remainder results actualRow n : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (lengthGraph n forwardRow)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix forwardRow)))
    (hl : Nonempty (Derivation body Delta (lengthGraph deletionCount deletionPrefix)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results deletionPrefix remainder)))
    (hs : Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.deletionRow actualRow childCount deletionCount results))) :
    Nonempty (Derivation body Delta (eqn actualRow forwardRow)) := by
  have hrev := OriginalReverseLengthInvolutionProof.actualLaws body alpha Delta forwardRow n deletionPrefix hf hr
  have he := valueUnique length n deletionCount (Fin.cons deletionPrefix Fin.elim0)
    (InternalApplicationStepPeelSupportProof.andLeft hrev) hl
  have hlen := outputTransport length n deletionCount (Fin.cons forwardRow Fin.elim0) he hf
  have hv := OriginalResultStackDeletionRowProof.actualRestoration body alpha Delta childCount deletionCount
    forwardRow deletionPrefix remainder results hlen hr ha
  exact valueUnique OriginalHereditaryResultStackProgram.deletionRow actualRow forwardRow
    (Fin.cons childCount (Fin.cons deletionCount (Fin.cons results Fin.elim0))) hs hv

theorem actual (forwardRow deletionPrefix childCount deletionCount remainder results actualRow : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix forwardRow)))
    (hl : Nonempty (Derivation body Delta (lengthGraph deletionCount deletionPrefix)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results deletionPrefix remainder)))
    (hs : Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.deletionRow actualRow childCount deletionCount results))) :
    Nonempty (Derivation body Delta (eqn actualRow forwardRow)) := by
  apply programCases length (Fin.cons forwardRow Fin.elim0) _
  intro beta j Theta n hj hn
  simp only [eqnRelabel]
  have hr' := renameInto hr j Theta hj
  have hl' := renameInto hl j Theta hj
  have ha' := renameInto ha j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [lengthGraph,graph1Rename,graph2Rename,graph3Rename] at hr' hl' ha' hs'
  simp only [consTermRename,emptyRename] at hn
  exact atLength (forwardRow.relabel j) (deletionPrefix.relabel j) (childCount.relabel j)
    (deletionCount.relabel j) (remainder.relabel j) (results.relabel j) (actualRow.relabel j) n hn hr' hl' ha' hs'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionSelectorContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionSelectorContentProof
