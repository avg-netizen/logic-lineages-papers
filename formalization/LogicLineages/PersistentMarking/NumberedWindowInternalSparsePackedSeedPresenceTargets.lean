module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceTargets

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- Successful selection at a seed forces that seed to occur in the
given actual cover projection at the same seed. -/
def ExactSeedInGivenVertices : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty seed minimum vertices : OTerm α),
    Nonempty (Derivation body Γ
      ((leastGraph C X W s ctx ty seed minimum ⊓ unary (scratchVertices C s) vertices seed).imp
        (memberGraph vertices seed)))

/-- Successful selection at a seed forces that seed to occur in the
given actual members pool on the identical packed program tape. -/
def ExactSeedInGivenPool : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty seed minimum pool : OTerm α),
    Nonempty (Derivation body Γ
      ((leastGraph C X W s ctx ty seed minimum ⊓
        programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed]).imp
        (memberGraph pool seed)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceTargets
