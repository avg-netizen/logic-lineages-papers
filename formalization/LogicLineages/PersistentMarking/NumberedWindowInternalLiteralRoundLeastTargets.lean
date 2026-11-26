module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets

@[expose] public section
namespace LogicLineages.PersistentMarking
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowScalarAlgorithm (Settings)

namespace NumberedWindowInternalLiteralRoundLeastTargets
/-- Both endpoints possess actual least values and every proposed common
value is accepted at one endpoint exactly when accepted at the other. -/
def SameLeastOnEdge (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b x : OTerm α),
    let source := leastGraph C X W s ctx ty a x
    let target := leastGraph C X W s ctx ty b x
    let both := hasLeast C X W s ctx ty a ⊓ hasLeast C X W s ctx ty b
    Nonempty (Derivation body Γ ((acceptEdge (edge4 X W) ctx ty a b).imp (both ⊓ equivalent source target)))

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

end NumberedWindowInternalLiteralRoundLeastTargets
end LogicLineages.PersistentMarking
