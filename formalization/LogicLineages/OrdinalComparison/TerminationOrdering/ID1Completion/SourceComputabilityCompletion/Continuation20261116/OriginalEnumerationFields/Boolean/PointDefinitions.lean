module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointRange
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open Continuation20261114.HeadWindowBooleanRange
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type} {k : Nat}
def matrix (p : Program k) (xs : Fin k → OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (programGraph p (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl)).imp (BooleanValue (.var (.inr 0)))
def At (p : Program k) (xs : Fin k → OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix p xs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointRange
