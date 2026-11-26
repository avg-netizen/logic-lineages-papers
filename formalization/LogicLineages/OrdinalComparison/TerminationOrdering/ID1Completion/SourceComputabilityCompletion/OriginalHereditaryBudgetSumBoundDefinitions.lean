module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBound
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalClosedPrograms (allBlock)
open OriginalContextInsertion
/-- Literal bounded numeric-list membership and actual budget observation. -/
def cellFields {alpha : Type} (count jobs branching index child value : OTerm alpha) : Formula alpha :=
 Below index count ⊓ (graph2 InternalRawListRecursion.lookup child index jobs ⊓
   graph2 OriginalHereditaryBudgetSum.jobBudget value child branching)
def cellMatrix {alpha : Type} (count jobs branching cap : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (cellFields (count.relabel Sum.inl) (jobs.relabel Sum.inl) (branching.relabel Sum.inl)
   (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
 (ltF (.var (.inr 2)) (suc (cap.relabel Sum.inl)))
def CellsBound {alpha : Type} (count jobs branching cap : OTerm alpha) : Formula alpha :=
 allBlock (cellMatrix count jobs branching cap)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBound
