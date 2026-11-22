module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoveredInstallationTargets (SameLeastOnEdge)
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)

def inputs {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (i vertices ctx ty seed out k m : OTerm α) : Formula α :=
  leastGraph C X W s ctx ty seed m ⊓
    (roundGraph (edge4 X W) out i vertices ctx ty seed ⊓ memberGraph out k)

/-- Every occurrence in an actual finite round has the original seed's chosen value. -/
def ExactRoundLeast : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings), SameLeastOnEdge C X W s →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (i vertices ctx ty seed out k m : OTerm α),
      Nonempty (Derivation body Γ ((inputs C X W s i vertices ctx ty seed out k m).imp
        (leastGraph C X W s ctx ty k m)))

/-- The successful output of the actual covered least program is its own successful output. -/
def ExactCoveredLeastIdempotent : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (baseW : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed m : OTerm α),
    let X := guardedExchange C s (pairedExchange baseX)
    let W := coveredWindow C s baseW
    Nonempty (Derivation body Γ ((leastGraph C X W s ctx ty seed m).imp (leastGraph C X W s ctx ty m m)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastTargets
