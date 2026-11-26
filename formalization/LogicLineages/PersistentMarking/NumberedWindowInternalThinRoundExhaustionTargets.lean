module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundChargeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundExhaustionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalThinRoundAlternativeTargets (budgetStep)
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)

def CountLengthBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices before count size : OTerm α),
    Nonempty (Derivation body Γ (graph2 NumberedWindowInternalThinUncoveredCount.count count vertices before)) →
    Nonempty (Derivation body Γ (unary poolLength size vertices)) →
    Nonempty (Derivation body Γ (NumberedWindowInternalThinUncoveredCount.bounded count size))

/-- The actual vertex-list length bounds the zero-time budget even for lists
with repeated entries and for the actual filtered initial round. -/
def ExactInitialBudget : Prop :=
  CountLengthBound →
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices size before after count : OTerm α),
    Nonempty (Derivation body Γ ((unary poolLength size vertices ⊓
      graph2 NumberedWindowInternalThinUncoveredCount.count count vertices before).imp
        (NumberedWindowInternalThinRoundChargeTargets.budget z size count before after)))

/-- At elapsed time equal to the initial allowance, the remaining count
cannot drop on this actual step. The supplied invariant then forces stability. -/
def ExactExhaustedBudget : Prop :=
  NumberedWindowInternalThinUncoveredCountTargets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed size before after countA countB : OTerm α),
    let step := budgetStep E vertices ctx ty seed size before after countA countB
    Nonempty (Derivation body Γ ((step ⊓ NumberedWindowInternalThinRoundChargeTargets.budget size size countA before after).imp
      (NumberedWindowInternalScratchInclusionThinProof.included after before)))

end LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundExhaustionTargets
