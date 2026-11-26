module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRoundAlternativeTargets (budgetStep)
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)

/-- The actual vertex-list length bounds the zero-time budget even for lists
with repeated entries and for the actual filtered initial round. -/
def ExactInitialBudget : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices size before after count : OTerm α),
    Nonempty (Derivation body Γ ((unary poolLength size vertices ⊓
      graph2 PrimaryUncoveredCount.count count vertices before).imp
        (PrimaryFiniteDescent.budget z size count before after)))

/-- At elapsed time equal to the initial allowance, the remaining count
cannot drop on this actual step. The supplied invariant then forces stability. -/
def ExactExhaustedBudget : Prop :=
  PrimaryUncoveredCount.Targets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed size before after countA countB : OTerm α),
    let step := budgetStep E vertices ctx ty seed size before after countA countB
    Nonempty (Derivation body Γ ((step ⊓ PrimaryFiniteDescent.budget size size countA before after).imp
      (PrimaryMonotonicity.included after before)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionTargets
