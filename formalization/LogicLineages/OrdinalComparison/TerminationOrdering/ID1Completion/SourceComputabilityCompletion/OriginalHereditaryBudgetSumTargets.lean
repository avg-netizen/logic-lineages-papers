module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalOrderSyntaxProof (ltF)
/-- Genuine aggregate expansion bound at one FIXED branching parameter. Includes
weight zero; no per-child bound, successful run or admissibility premise. This
alone does not imply runtime completion on malformed annotation jobs. -/
def ActualLocalBound : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent jobs weight branching total parentBudget : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight parent)) →
 Nonempty (Derivation body Delta (ltF (suc (suc weight)) (suc branching))) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum total jobs branching)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget parentBudget weight branching)) →
 Nonempty (Derivation body Delta (ltF total parentBudget))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumTargets
