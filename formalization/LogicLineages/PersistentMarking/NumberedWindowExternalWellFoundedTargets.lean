import LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowPositiveSimulationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedTargets
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass

def ActualPositiveRelationWellFounded : Prop :=
  ∀ S K Γ τ, DecisionSourceUniverse.Closed K →
    WellFounded (fun r q : Class S K (finiteC Γ) τ => RS S K (finiteC Γ) τ q r)

def ConfinedStrictWellFounded : Prop :=
  ∀ S, WellFounded (fun t s : Spine.Expr => ConfinedPair.Strict S s t)

end LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedTargets
