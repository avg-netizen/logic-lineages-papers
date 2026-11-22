module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundBudgetTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

def budgetStep {α : Type} (E : Program 4)
    (vertices ctx ty seed fuel before after beforeCount afterCount : OTerm α) : Formula α :=
  (roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed) ⊓
    (graph2 PrimaryUncoveredCount.count beforeCount vertices before ⊓
      graph2 PrimaryUncoveredCount.count afterCount vertices after)

def drops {α : Type} (afterCount beforeCount : OTerm α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula afterCount beforeCount)

/-- In the actual Paper 16 iteration, either every member of the next list
already belongs to the previous list, or the true uncovered count decreases. -/
def ExactRoundAlternative : Prop :=
  PrimaryUncoveredCount.Targets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed fuel before after beforeCount afterCount : OTerm α),
    Nonempty (Derivation body Γ ((budgetStep E vertices ctx ty seed fuel before after beforeCount afterCount).imp
      (PrimaryMonotonicity.included after before ⊔ drops afterCount beforeCount)))

/-- Without strict decrease, every accepted outgoing edge to an original
vertex from a member of the old pool already lands in the old pool. -/
def ExactClosedWithoutDecrease : Prop :=
  PrimaryUncoveredCount.Targets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed fuel before after beforeCount afterCount w k : OTerm α),
    let step := budgetStep E vertices ctx ty seed fuel before after beforeCount afterCount
    let edge := (memberGraph before w ⊓ acceptEdge E ctx ty w k) ⊓ memberGraph vertices k
    Nonempty (Derivation body Γ ((step ⊓ ((drops afterCount beforeCount).not ⊓ edge)).imp
      (memberGraph before k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeTargets
