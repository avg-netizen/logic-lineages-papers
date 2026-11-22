module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalLessThan (strictLess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)

/-- A seed present in the original vertices survives every round, with
arbitrary open fuel and output of the actual rounds program. -/
def ExactSeedEveryRound : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out fuel vertices ctx ty seed : OTerm α),
    Nonempty (Derivation body Γ ((roundGraph E out fuel vertices ctx ty seed ⊓ memberGraph vertices seed).imp
      (memberGraph out seed)))

/-- A successful original packed least is at most its input seed if that
seed occurs in its own actual cover. No members, fuel or minimum graph is supplied. -/
def ExactPackedSeedBound : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty seed vertices minimum : OTerm α),
    let cover := programGraph (poolAtSeed C s) vertices ![ctx,ty,seed]
    Nonempty (Derivation body Γ ((leastGraph C X W s ctx ty seed minimum ⊓
      (cover ⊓ memberGraph vertices seed)).imp (strictLess seed minimum).not))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundTargets
