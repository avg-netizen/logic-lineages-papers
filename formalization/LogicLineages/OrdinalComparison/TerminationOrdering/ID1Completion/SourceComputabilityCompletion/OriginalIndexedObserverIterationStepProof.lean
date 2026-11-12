module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalIndexedObserverIteration
open InternalGraphComposition InternalApplicationCertificateConstructors
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem forwardStep (data : Data) (supply : Preservation data) (out input parameter indicator cutoff : OTerm α)
    (hRange : Nonempty (Derivation body Gamma (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hb : Nonempty (Derivation body Gamma (markGraph data indicator input parameter cutoff)))
    (ht : Nonempty (Derivation body Gamma (graph2 (step data) out input parameter))) :
    Nonempty (Derivation body Gamma (markGraph data indicator out parameter cutoff)) := by
  obtain ⟨hi⟩ := supply body α Gamma out input parameter indicator cutoff hRange ha ht
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hb⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationStepProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationStepProof
