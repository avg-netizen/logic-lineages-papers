module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinFuelBudgetTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseDirectedRounds (poolLength members membersTape)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinFuelBudgetTargets (runsAt)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

/-- The real original count bound and strict drop are held exact object
theorems, as is the directed retained predecessor. -/
def ExactLengthStableFromPredecessor : Prop :=
  CountLengthBound → ExactRetainedPredecessor → NumberedWindowInternalThinUncoveredCountTargets.InternalStrictDecrease → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed size before after : OTerm α),
    Nonempty (Derivation body Γ ((unary poolLength size vertices ⊓
      runsAt E size vertices ctx ty seed before after).imp (NumberedWindowInternalScratchInclusionThinProof.included after before)))

/-- The actual members output is closed under every accepted directed edge
from a contained source to a destination among the same original vertices. -/
def ExactMembersEdgeClosure : Prop :=
  CountLengthBound → ExactRetainedPredecessor → NumberedWindowInternalThinUncoveredCountTargets.InternalStrictDecrease → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed pool source target : OTerm α),
    let run := programGraph (members E) pool (membersTape vertices ctx ty seed)
    let edge := (memberGraph pool source ⊓ acceptEdge E ctx ty source target) ⊓ memberGraph vertices target
    Nonempty (Derivation body Γ ((run ⊓ edge).imp (memberGraph pool target)))

end LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureTargets
