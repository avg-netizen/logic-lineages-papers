module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SortWeightedDefinitions
/-- Exact insertion adds exactly the weight of the inserted entry. All three
premises are actual original computations with SAME arbitrary internal parameters; no sortedness, decoded permutation,
comparison result, or desired inserted sum is supplied. -/
def ActualInsertion : Prop := ∀ (k : Nat) (F : Program (k + 1)) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (raw x inserted weight sum : OTerm alpha) (params : Fin k → OTerm alpha),
 Nonempty (Derivation body Delta (graph2 OriginalNumericListSort.insert inserted raw x)) →
 Nonempty (Derivation body Delta (programGraph F weight (Fin.cons x params))) →
 Nonempty (Derivation body Delta (programGraph (weighted F) sum (Fin.cons raw params))) →
 Nonempty (Derivation body Delta (programGraph (weighted F) (add weight sum) (Fin.cons inserted params)))
/-- The unchanged original insertion-sort preserves arbitrary weighted sums,
including multiplicity. This is a prerequisite only, NOT evaluator rank
determinacy, native Perm reflection, or a canonical Object assertion. -/
def ActualSort : Prop := ∀ (k : Nat) (F : Program (k + 1)) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (raw sorted sum : OTerm alpha) (params : Fin k → OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted raw)) →
 Nonempty (Derivation body Delta (programGraph (weighted F) sum (Fin.cons raw params))) →
 Nonempty (Derivation body Delta (programGraph (weighted F) sum (Fin.cons sorted params)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedTargets
