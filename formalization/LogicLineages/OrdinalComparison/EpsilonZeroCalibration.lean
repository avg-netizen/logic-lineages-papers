module
public import LogicLineages.OrdinalComparison.OrdinalRepresentationTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem epsilonZeroCalibration : Targets.EpsilonZeroCalibration := by
  have hnormal := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  refine ⟨Ordinal.nfp_fp hnormal 0, ?_⟩
  intro b hb
  exact Ordinal.nfp_le_fp hnormal.monotone (show (0 : Ordinal) ≤ b from bot_le) hb.le

end LogicLineages.OrdinalComparison
