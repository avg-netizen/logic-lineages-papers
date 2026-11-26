module
public import LogicLineages.PermittedControl.ActualHighTailNormalizationTargets
import LogicLineages.PermittedControl.ActualFiniteGlobalTailProof
import LogicLineages.PermittedControl.ActualReadChargeIterationProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualHighTailNormalization
open ActualReadChargeIteration ActualFiniteGlobalTail

theorem exactActualHighTailNormalization : ExactActualHighTailNormalization := by
  intro f B selected ρ strict r zRank initial reads bounded long high
  exact exactReadChargeIteration f B selected ρ strict r zRank initial reads bounded
    (exactGlobalGuardSupply f B ρ r zRank initial reads long high)

end LogicLineages.PermittedControl.ActualHighTailNormalization
