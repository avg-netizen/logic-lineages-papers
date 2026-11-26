module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountRowStepTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionConsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountBranchTargets (SideCountCongruence)
open NumberedWindowInternalProjectedCountInductionTargets (reportMatrix atRows compared)

def ExactOpenProjectedCountInductionCons : Prop :=
  SideCountCongruence true → SideCountCongruence false →
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code row tail pool fl fr p pl pr joined : OTerm α),
    D B Γ (consGraph code row tail) → D B Γ (atRows tail pool) →
    D B Γ (reportMatrix code pool fl fr p pl pr joined) → D B Γ (compared p joined)

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionConsTargets
