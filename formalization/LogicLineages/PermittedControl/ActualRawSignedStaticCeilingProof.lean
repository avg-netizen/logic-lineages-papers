module
public import LogicLineages.PermittedControl.ActualRawSignedStaticCeilingTargets
import LogicLineages.PermittedControl.ActualRawComparisonCeilingProof
import LogicLineages.PermittedControl.ActualBitFamilyRawReadCeilingProof
import LogicLineages.PermittedControl.ActualEffectiveGlobalTailDominanceProof
import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundDominanceProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawSignedStaticCeiling
open ActualPaidSignedRouteReplay (commonMinimum dummy)
open ActualFiniteGlobalTail (syntaxOf)
open ActualRawComparisonCeiling (budgetCalibration)
open ActualEffectiveGlobalTail (exactTailDominance)
open ActualEffectiveTerminalSignBound (exactSignBoundDominance)
open ActualBitFamilyRawReadCeiling (termsCalibration)

theorem exactCommonMinimumMajorant : ExactCommonMinimumMajorant := by
  intro B r s
  unfold commonCode encodeSyntax commonMinimum
  rw [termsCalibration,budgetCalibration]
  exact max_le_max le_rfl (max_le_max (exactTailDominance.1 B r s.terms) le_rfl)

theorem exactTerminalCutoffMajorant : ExactTerminalCutoffMajorant := by
  intro r s
  have tape : syntaxOf (dummy s) = s.terms := by
    change (s.terms.map (fun t => (t,(0 : Nat)))).map Prod.fst = s.terms
    simp only [List.map_map,Function.comp_def,List.map_id']
  have bound := exactSignBoundDominance r (dummy s)
  rw [tape] at bound
  exact bound

theorem exactRawSignedStaticMajorant : ExactRawSignedStaticMajorant := by
  intro B r s
  exact max_le_max (exactCommonMinimumMajorant B r s) (exactTerminalCutoffMajorant r s)

end LogicLineages.PermittedControl.ActualRawSignedStaticCeiling
