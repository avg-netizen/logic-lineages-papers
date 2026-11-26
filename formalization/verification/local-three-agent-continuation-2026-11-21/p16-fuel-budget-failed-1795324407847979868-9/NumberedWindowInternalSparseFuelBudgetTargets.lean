module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

def runsAt {α : Type} (E : Program 4) (fuel vertices ctx ty seed before after : OTerm α) : Formula α :=
  roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed

def inputs {α : Type} (E : Program 4) (fuel vertices ctx ty seed size before after count : OTerm α) : Formula α :=
  (unary poolLength size vertices ⊓ graph2 PrimaryUncoveredCount.count count vertices before) ⊓
    runsAt E fuel vertices ctx ty seed before after

/-- An object-calculus budget holds at every open fuel of the actual
Paper 16 rounds on the actual length and uncovered occurrence count. -/
def ExactFuelBudget : Prop :=
  ExactRetainedPredecessor → PrimaryUncoveredCount.Targets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (fuel vertices ctx ty seed size before after count : OTerm α),
    Nonempty (Derivation body Γ ((inputs E fuel vertices ctx ty seed size before after count).imp
      (PrimaryFiniteDescent.budget fuel size count before after)))

/-- On the original list-length round, every member of its actual successor
was present already. No count graph or precomputed budget is an input. -/
def ExactLengthStability : Prop :=
  ExactRetainedPredecessor → PrimaryUncoveredCount.Targets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed size before after : OTerm α),
    Nonempty (Derivation body Γ ((unary poolLength size vertices ⊓
      runsAt E size vertices ctx ty seed before after).imp (PrimaryMonotonicity.included after before)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetTargets
