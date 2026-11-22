module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseDirectedRounds (poolLength members membersTape)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFuelBudgetTargets (runsAt)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

/-- The strict uncovered-count theorem is supplied by the original native
checked comparison. Only the directed retained predecessor remains. -/
def ExactLengthStableFromPredecessor : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed size before after : OTerm α),
    Nonempty (Derivation body Γ ((unary poolLength size vertices ⊓
      runsAt E size vertices ctx ty seed before after).imp (PrimaryMonotonicity.included after before)))

/-- The actual members output is closed under every accepted directed edge
from a contained source to a destination among the same original vertices. -/
def ExactMembersEdgeClosure : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed pool source target : OTerm α),
    let run := programGraph (members E) pool (membersTape vertices ctx ty seed)
    let edge := (memberGraph pool source ⊓ acceptEdge E ctx ty source target) ⊓ memberGraph vertices target
    Nonempty (Derivation body Γ ((run ⊓ edge).imp (memberGraph pool target)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureTargets
