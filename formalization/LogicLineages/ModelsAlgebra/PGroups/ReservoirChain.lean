module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChainTargets
public import LogicLineages.ModelsAlgebra.PGroups.FreshCombine
public import Mathlib.Data.Finset.Lattice.Fold
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem reservoir_monotone : Targets.groupReservoirMonotone := by
  intro A B C _ _ _ i k hik x hx n hn
  exact hx n (hik.trans hn)

theorem reservoir_cover : Targets.groupReservoirCover := by
  intro A B C _ _ _ x
  refine ⟨x.2.1.support.sup id + 1, ?_⟩
  intro n hn
  by_contra hne
  have hs := Finsupp.mem_support_iff.mpr hne
  have hb : n ≤ _ := Finset.le_sup (f := id) hs
  omega

theorem reservoir_map_injective : Targets.groupReservoirMapInjective := by
  intro A B C _ _ _ i M j hj x y h
  have ha := congrArg (fun z : reservoirStage A B C i => z.val.1) h
  have hp := congrArg (fun z : reservoirStage A B C i => z.val.2.1) h
  have hh := congrArg (fun z : reservoirStage A B C i => z.val.2.2) h
  have ht : ((x.2.1.filter (fun n => i ≤ n)), x.2.2) =
      ((y.2.1.filter (fun n => i ≤ n)), y.2.2) :=
    fresh_combine_injective B C M j hj hh
  change x.1 = y.1 at ha
  apply Prod.ext ha
  apply Prod.ext
  swap
  · have he := congrArg (fun z : (ℕ →₀ B) × (ℕ →₀ C) => z.2) ht
    exact he
  ext n
  by_cases hn : n < i
  · have he := congrArg (fun z : ℕ →₀ B => z n) hp
    change (if n < i then x.2.1 n else 0) = (if n < i then y.2.1 n else 0) at he
    simpa [hn] using he
  · have he := congrArg (fun z : (ℕ →₀ B) × (ℕ →₀ C) => z.1 n) ht
    simpa [Finsupp.filter_apply, Nat.le_of_not_gt hn] using he

theorem reservoir_map_fixes : Targets.groupReservoirMapFixes := by
  intro A B C _ _ _ i M j x hx
  have ht : x.val.2.1.filter (fun n => i ≤ n) = 0 := by
    ext n
    by_cases hn : i ≤ n
    · simp [Finsupp.filter_apply, hn, x.property n hn]
    · simp [Finsupp.filter_apply, hn]
  have hp : x.val.2.1.filter (fun n => n < i) = x.val.2.1 := by
    ext n
    by_cases hn : n < i
    · simp [Finsupp.filter_apply, hn]
    · simp [Finsupp.filter_apply, hn, x.property n (Nat.le_of_not_gt hn)]
  apply Subtype.ext
  change (x.val.1, (x.val.2.1.filter (fun n => n < i),
    freshCombine B C M j (x.val.2.1.filter (fun n => i ≤ n), x.val.2.2))) = x.val
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact hp
  change freshCombine B C M j (x.val.2.1.filter (fun n => i ≤ n), x.val.2.2) = x.val.2.2
  rw [ht]
  exact fresh_combine_fixes B C M j x.val.2.2 hx

theorem reservoir_tuple_fixing : Targets.groupReservoirTupleFixing := by
  classical
  intro A B C _ _ _ j hj i m d
  let support := Finset.univ.biUnion (fun a : Fin m => (d a).val.2.2.support)
  let M := support.sup id + 1
  refine ⟨reservoirStageMap A B C i M j, reservoir_map_injective A B C i M j hj, ?_⟩
  intro a
  apply reservoir_map_fixes A B C i M j (d a)
  intro n hn
  have hs : n ∈ support := Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hn⟩
  have hb : n ≤ _ := Finset.le_sup (f := id) hs
  dsimp [M]
  omega

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
