module

public import LogicLineages.NativeModule.PersistentMarking.ActualTowerIndexTargets
import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationTwoProof

public section

namespace LogicLineages.PersistentMarking.ActualTowerIndexProof
open Ordinal ActualOmegaTower ActualCollapse ActualCalibration ActualTowerIndex
open scoped Ordinal

theorem exact_TowerIndexFacts : TowerIndexFacts := by
  intro k
  induction k with
  | zero =>
    have arg2 : argument 2 = omegaIndex := exact_LiteralRecurrence.2.2.2.1
    refine ⟨fun e he => ?_, fun e _ he => ?_, fun η e hη _ _ hn => ?_⟩
    · show e < argument 2
      rw [arg2]
      exact he
    · show coefficientNorm e ≤ e
      exact (norm_countable e (show e < ω₁ from he)).le
    · show η < e
      have hη' : η < argument 2 := hη
      rw [arg2] at hη'
      rwa [norm_countable η (show η < ω₁ from hη')] at hn
  | succ k ih =>
    obtain ⟨below, normLe, cover⟩ := ih
    have argS : argument (k + 1 + 2) = omegaIndex ^ argument (k + 2) := argument_succ (k + 2)
    refine ⟨fun e he => ?_, fun e h1 he => ?_, fun η e hη h1 he hn => ?_⟩
    · show omegaIndex ^ towerIndex k e < argument (k + 1 + 2)
      rw [argS]
      exact (opow_lt_opow_iff_right one_lt_index).2 (below e he)
    · show coefficientNorm (omegaIndex ^ towerIndex k e) ≤ e
      rw [norm_eq, cnf_power]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      refine max_le (max_le h1 ?_) (zero_le_one.trans h1)
      split
      · exact normLe e h1 he
      · exact zero_le_one.trans h1
    · show η < omegaIndex ^ towerIndex k e
      have hηtop : η < omegaIndex ^ argument (k + 2) := by rwa [argS] at hη
      rcases eq_or_ne η 0 with h0 | h0
      · rw [h0]
        exact opow_pos _ (zero_lt_one.trans one_lt_index)
      · have logLt : log omegaIndex η < argument (k + 2) :=
          (lt_opow_iff_log_lt one_lt_index h0).1 hηtop
        have mem : (log omegaIndex η, η / omegaIndex ^ log omegaIndex η) ∈ CNF omegaIndex η := by
          rw [CNF.ne_zero h0]
          exact List.mem_cons_self
        have hΛ : η < endpoint := hη.trans (exact_BelowEndpoint (k + 1 + 2))
        have he' : coefficientNorm (log omegaIndex η) ≤ coefficientNorm η := (entry_le hΛ mem).2.2
        exact (lt_opow_iff_log_lt one_lt_index h0).2
          (cover (log omegaIndex η) e logLt h1 he (lt_of_le_of_lt he' hn))

#print axioms exact_TowerIndexFacts

end LogicLineages.PersistentMarking.ActualTowerIndexProof
