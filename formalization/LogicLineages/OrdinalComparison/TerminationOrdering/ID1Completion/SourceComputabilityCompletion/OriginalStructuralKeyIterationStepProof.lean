module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalStructuralKeyIteration
open InternalGraphComposition InternalApplicationCertificateConstructors
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem forwardStep (data : Data) (supply : Preservation data) (out input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hb : Nonempty (Derivation body Gamma (markGraph data indicator input parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 (step data) out input parameter))) :
    Nonempty (Derivation body Gamma (markGraph data indicator out parameter)) := by
  obtain ⟨hi⟩ := supply body α Gamma out input parameter indicator ha ht
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hb⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationStepProof
