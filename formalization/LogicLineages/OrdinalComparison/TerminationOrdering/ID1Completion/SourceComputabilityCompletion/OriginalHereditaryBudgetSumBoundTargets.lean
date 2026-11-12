module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalMultiplicationLawsProof (mul)
open OriginalContextInsertion OriginalHereditaryBudgetSumBound
/-- Generic internal list majorization. CellsBound is a bounded arithmetic
formula, not a metalevel/native assertion. The final expansion target must
and will derive it from actual expansion lookup decrease. -/
def Majorization : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count jobs branching cap total : OTerm alpha),
 Nonempty (Derivation body Delta (lengthGraph count jobs)) →
 Nonempty (Derivation body Delta (CellsBound count jobs branching cap)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum total jobs branching)) →
 Nonempty (Derivation body Delta (ltF total (suc (mul count cap))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundTargets
