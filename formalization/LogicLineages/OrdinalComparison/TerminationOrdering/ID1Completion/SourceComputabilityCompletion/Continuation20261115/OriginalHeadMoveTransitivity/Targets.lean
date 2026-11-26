module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- Transitivity of the exact six-input original headMove checker under the SAME
symbols/types window, on arbitrary numeric heads and spines. All four original
guards are recovered from the two actual acceptances; none is assumed anew. -/
def InternalTransitivity : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (sourceHead sourceBase middleHead middleBase targetHead targetBase symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![sourceHead,sourceBase,middleHead,middleBase,symbols,types])) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![middleHead,middleBase,targetHead,targetBase,symbols,types])) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![sourceHead,sourceBase,targetHead,targetBase,symbols,types]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.Targets
