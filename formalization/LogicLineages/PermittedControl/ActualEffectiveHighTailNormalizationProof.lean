module
public import LogicLineages.PermittedControl.ActualEffectiveHighTailNormalizationTargets
import LogicLineages.PermittedControl.ActualHighTailNormalizationProof
import LogicLineages.PermittedControl.ActualEffectiveGlobalTailDominanceProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveHighTailNormalization
open ActualFiniteGlobalTail ActualEffectiveGlobalTail ActualHighTailNormalization

theorem exactActualEffectiveHighTailNormalization : ExactActualEffectiveHighTailNormalization := by
  intro f B selected ρ strict r zRank initial reads bounded long paid
  exact exactActualHighTailNormalization f B selected ρ strict r zRank initial reads bounded long
    (exactTailDominance.2 B r ρ (syntaxOf initial) paid)

end LogicLineages.PermittedControl.ActualEffectiveHighTailNormalization
