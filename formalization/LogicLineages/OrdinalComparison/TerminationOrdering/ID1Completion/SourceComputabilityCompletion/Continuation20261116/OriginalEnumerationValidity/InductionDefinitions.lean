module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open Continuation20261115
variable {alpha : Type}
/-- Actual original fuel R(node), universally over arbitrary node/parameter/output.
The conclusion quantifies every member internally, not only a literal candidate. -/
def matrix (n : Nat) (fuel : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (graph2 OriginalEnumerationRecursionInterface.R (fuel.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) ⊓
    graph2 (OriginalEnumerationRecursion.enumeration n) (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1))).imp
    (Lists.AllValid n (.var (.inr 2)))
def AtRank (n : Nat) (fuel : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix n fuel)
def predicate (n : Nat) : Formula (alpha ⊕ Fin 1) := AtRank n (.var (.inr 0))
def BelowRank (n : Nat) (fuel : OTerm alpha) : Formula alpha := InternalStrongInduction.below (predicate n) fuel
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity
