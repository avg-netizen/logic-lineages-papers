module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormTargets
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem cnfDescentBelowEpsilonZero : Targets.CNFDescentBelowEpsilonZero := by
  intro a ha p hp
  have hzero : a ≠ 0 := by
    intro h
    subst a
    simpa only [Ordinal.CNF.zero_right, List.not_mem_nil] using hp
  exact ⟨(Ordinal.CNF.fst_le_log hp).trans_lt
    (omega_log_lt_below_epsilonZero a ha hzero),
    Ordinal.CNF.snd_pos hp, Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hp⟩

end LogicLineages.OrdinalComparison
