module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)

/-- The actual initial seed occurs at round zero iff it was present in the
original vertices. This statement requires no supplied singleton code. -/
def ExactSeedRoundZero : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out vertices ctx ty seed : OTerm α),
    let was := memberGraph vertices seed
    let now := memberGraph out seed
    Nonempty (Derivation body Γ ((roundGraph E out z vertices ctx ty seed).imp
      ((was.imp now) ⊓ (now.imp was))))

/-- A real edge from an actual member extends reachability by one round,
when its target occurs in those same original vertices. -/
def ExactRoundEdgeExtension : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (before after fuel vertices ctx ty seed w k : OTerm α),
    let stages := roundGraph E before fuel vertices ctx ty seed ⊓
      roundGraph E after (suc fuel) vertices ctx ty seed
    let step := (memberGraph before w ⊓ acceptEdge E ctx ty w k) ⊓ memberGraph vertices k
    Nonempty (Derivation body Γ ((stages ⊓ step).imp (memberGraph after k)))

/-- Every member of the previous output is retained in the genuine next
output, without a separately supplied input-vertices membership proof. -/
def ExactAdjacentRoundPersistence : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (before after fuel vertices ctx ty seed k : OTerm α),
    let stages := roundGraph E before fuel vertices ctx ty seed ⊓
      roundGraph E after (suc fuel) vertices ctx ty seed
    Nonempty (Derivation body Γ ((stages ⊓ memberGraph before k).imp (memberGraph after k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets
