module
public import LogicLineages.ModelsAlgebra.PGroups.FreshCombineTargets
public import LogicLineages.ModelsAlgebra.PGroups.FreshCoordinates
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem fresh_combine_odd : Targets.groupFreshCombineOdd := by
  intro B C _ _ M j x y n
  have hz : Finsupp.mapDomain (reserveEven M) y (reserveOdd M n) = 0 :=
    Finsupp.mapDomain_notin_range y _ (by
      intro h
      exact Set.disjoint_left.mp (reserve_ranges_disjoint M) h ⟨n,rfl⟩)
  change Finsupp.mapDomain (reserveOdd M) (Finsupp.mapRange j (map_zero j) x) (reserveOdd M n) +
    Finsupp.mapDomain (reserveEven M) y (reserveOdd M n) = j (x n)
  rw [Finsupp.mapDomain_apply (reserve_odd_injective M), hz, add_zero]
  rfl

theorem fresh_combine_even : Targets.groupFreshCombineEven := by
  intro B C _ _ M j x y n
  have hz : Finsupp.mapDomain (reserveOdd M) (Finsupp.mapRange j (map_zero j) x) (reserveEven M n) = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by
      intro h
      exact Set.disjoint_left.mp (reserve_ranges_disjoint M) ⟨n,rfl⟩ h)
  change Finsupp.mapDomain (reserveOdd M) (Finsupp.mapRange j (map_zero j) x) (reserveEven M n) +
    Finsupp.mapDomain (reserveEven M) y (reserveEven M n) = y n
  rw [hz, Finsupp.mapDomain_apply (reserve_even_injective M), zero_add]

theorem fresh_combine_injective : Targets.groupFreshCombineInjective := by
  intro B C _ _ M j hj x y h
  apply Prod.ext
  · ext n
    apply hj
    have he := congrArg (fun z : ℕ →₀ C => z (reserveOdd M n)) h
    simpa only [fresh_combine_odd B C M j x.1 x.2 n,
      fresh_combine_odd B C M j y.1 y.2 n] using he
  · ext n
    have he := congrArg (fun z : ℕ →₀ C => z (reserveEven M n)) h
    simpa only [fresh_combine_even B C M j x.1 x.2 n,
      fresh_combine_even B C M j y.1 y.2 n] using he

theorem fresh_combine_fixes : Targets.groupFreshCombineFixes := by
  intro B C _ _ M j y h
  have he : Finsupp.mapDomain (reserveEven M) y = y := by
    calc
      _ = Finsupp.mapDomain id y := Finsupp.mapDomain_congr (fun n hn => reserve_even_fixes M n (h n hn))
      _ = y := Finsupp.mapDomain_id
  simpa [freshCombine] using he

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
