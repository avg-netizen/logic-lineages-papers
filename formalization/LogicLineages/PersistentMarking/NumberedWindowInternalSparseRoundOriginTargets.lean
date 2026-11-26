module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (seenWitness)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

/-- Every candidate in the zero round arises from the actual singleton seed
and the same source vertices. The zero edge has no successful call. -/
def ExactZeroRoundOrigin : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out vertices ctx ty seed k : OTerm α),
    let origin := memberGraph vertices seed ⊓ eqn seed k
    let candidate := memberGraph out k
    Nonempty (Derivation body Γ ((roundGraph E out z vertices ctx ty seed).imp
      ((candidate.imp origin) ⊓ (origin.imp candidate))))

/-- Exact successor characterization over the genuine prior output, with the
original unprojected predecessor existential and an independent vertex guard. -/
def ExactSuccessorRoundOrigin : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (before after fuel vertices ctx ty seed k : OTerm α),
    let stages := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
    let origin := memberGraph vertices k ⊓ seenWitness E before ctx ty k
    let candidate := memberGraph after k
    Nonempty (Derivation body Γ (stages.imp ((candidate.imp origin) ⊓ (origin.imp candidate))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginTargets
