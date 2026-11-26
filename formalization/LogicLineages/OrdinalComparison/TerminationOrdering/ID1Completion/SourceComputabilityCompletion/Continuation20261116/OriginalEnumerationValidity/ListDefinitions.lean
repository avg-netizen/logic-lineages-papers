module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Lists
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115
variable {alpha : Type}
def matrix (n : Nat) (list : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (graph2 contains (numeral 1) (list.relabel Sum.inl) (.var (.inr 0))).imp
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) (.var (.inr 0)))
def AllValid (n : Nat) (list : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n list)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Lists
