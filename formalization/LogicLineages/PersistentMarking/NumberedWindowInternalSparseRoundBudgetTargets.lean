module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Targets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundBudgetTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.SourceComputabilityCompletion
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)

def ExactBudgetPrograms : Prop :=
  scratchMember = TwoSol20261113.CalibratedPrimary.Membership.contains ∧
  poolLength = OriginalContextInsertion.length

/-- The inclusion quantified in the original finite arithmetic potential
applies to the two successive physical Paper 16 rounds. -/
def ExactBudgetInclusion : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (before after fuel vertices ctx ty seed : OTerm α),
    Nonempty (Derivation body Γ ((roundGraph E before fuel vertices ctx ty seed ⊓
      roundGraph E after (suc fuel) vertices ctx ty seed).imp (PrimaryMonotonicity.included before after)))

/-- An actual newly discovered member, in the same original pool, pays the
original strict decrease of the unreached occurrence count on these rounds. -/
def ExactNewMemberDecrease : Prop :=
  PrimaryUncoveredCount.Targets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (before after fuel vertices ctx ty seed beforeCount afterCount k : OTerm α),
    let stages := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
    let counts := graph2 PrimaryUncoveredCount.count beforeCount vertices before ⊓
      graph2 PrimaryUncoveredCount.count afterCount vertices after
    let fresh := (memberGraph before k).not ⊓ memberGraph after k
    Nonempty (Derivation body Γ ((stages ⊓ (counts ⊓ fresh)).imp
      (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula afterCount beforeCount))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundBudgetTargets
