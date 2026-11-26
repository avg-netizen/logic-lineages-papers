module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Induction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115
variable {alpha : Type}
/-- Exact frozen graph observations, with actual original fuel fixed externally.
All eleven remaining arithmetic inputs are universally quantified internally. -/
def matrix (n : Nat) (fuel : OTerm alpha) : Formula (alpha ⊕ Fin 11) :=
  let v (i : Fin 11) : OTerm (alpha ⊕ Fin 11) := .var (.inr i)
  let observations := graph2 InternalPairing.pairing (v 0) (v 6) (fuel.relabel Sum.inl) ⊓
    graph2 InternalPairing.pairing (v 1) (v 7) (v 2) ⊓
    graph2 InternalPairing.pairing (v 2) (v 8) (v 3) ⊓
    graph2 InternalPairing.pairing (v 3) (v 9) (v 10) ⊓
    graph2 (OriginalEnumerationRecursion.enumeration n) (v 4) (v 0) (v 1)
  let member := graph2 contains (numeral 1) (v 4) (v 5)
  let meaning := Meaning.holds n (v 5) (v 6) (fuel.relabel Sum.inl) (v 7) (v 8) (v 9) (v 10)
  observations.imp ((member.imp meaning) ⊓ (meaning.imp member))
def AtFuel (n : Nat) (fuel : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix n fuel)
def predicate (n : Nat) : Formula (alpha ⊕ Fin 1) := AtFuel n (.var (.inr 0))
def BelowFuel (n : Nat) (fuel : OTerm alpha) : Formula alpha := InternalStrongInduction.below (predicate n) fuel
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Induction
