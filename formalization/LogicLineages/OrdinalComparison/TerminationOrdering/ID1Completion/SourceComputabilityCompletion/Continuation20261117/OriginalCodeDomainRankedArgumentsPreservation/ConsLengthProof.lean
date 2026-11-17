module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ConsLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof (cancelSuc symm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tailLength (list head tail count : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length (suc count) list))) :
    Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count tail)) := by
  apply programCases OriginalContextInsertion.length ![tail] _
  intro beta j Theta c hj ht
  simp only [graph1Rename]
  have hv : (fun i => (![tail] i).relabel j) = ![tail.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hv] at ht
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hl' := renameInto hl j Theta hj
  simp only [graph1Rename,sucRelabel] at hl'
  obtain ⟨he⟩ := OriginalContextInsertionLengthProof.lengthConsRecover (list.relabel j)
    (head.relabel j) (tail.relabel j) (suc (count.relabel j)) c hc' hl' ht
  exact outputTransport OriginalContextInsertion.length c (count.relabel j) ![tail.relabel j]
    ⟨symm (cancelSuc he)⟩ ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ConsLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ConsLengthProof
