module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalOrderSyntaxProof (ltF)
/-- Same-depth branching monotonicity of the actual numeric budget, including zero. -/
def Monotone : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (depth b c v w : OTerm alpha),
 Nonempty (Derivation body Delta (ltF b (suc c))) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget v depth b)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget w depth c)) →
 Nonempty (Derivation body Delta (ltF v (suc w)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchTargets
