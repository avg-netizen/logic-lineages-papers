module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open Continuation20261114.HeadWindowBooleanRange
variable {alpha : Type}
/-- Genuine projected-raw rank: every key and parameter with this actual rank.
No recursive acceptance or native interpretation is assumed. -/
def matrix (n : Nat) (r : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (graph2 rank (r.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) ⊓
    graph2 (extract n) (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1))).imp
    (BooleanValue (.var (.inr 2)))
def AtRank (n : Nat) (r : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix n r)
def predicate (n : Nat) : Formula (alpha ⊕ Fin 1) := AtRank n (.var (.inr 0))
def BelowRank (n : Nat) (r : OTerm alpha) : Formula alpha := InternalStrongInduction.below (predicate n) r
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean
