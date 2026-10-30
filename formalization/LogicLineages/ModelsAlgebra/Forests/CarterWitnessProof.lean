module

public import LogicLineages.ModelsAlgebra.Forests.CarterWitnessTargets
public import LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof

/-! Literal enumeration gives bounded same-state representatives and an actual
accepted-tree witness, rather than only existential language nonemptiness. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof

open CarterAutomata CarterAutomataProof

theorem carterTreeEnumerationExact : Targets.CarterTreeEnumerationExact := by
  intro k n
  induction n with
  | zero =>
      intro t
      cases t <;> simp [treesUpTo, height]
  | succ n ih =>
      intro t
      cases t <;>
        simp [treesUpTo, List.mem_flatMap, List.mem_map, ih, height, Nat.add_comm] <;> omega

theorem carterTreeSizeBound : Targets.CarterTreeSizeBound := by
  intro k t
  induction t with
  | leaf a => simp [vertexCount, height]
  | node a l r ihl ihr =>
      have hl : 2 ^ height l ≤ 2 ^ max (height l) (height r) :=
        Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)
      have hr : 2 ^ height r ≤ 2 ^ max (height l) (height r) :=
        Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
      simp only [vertexCount, height, pow_add, pow_one]
      omega

theorem carterBoundedRunRepresentative : Targets.CarterBoundedRunRepresentative := by
  intro k q M t
  obtain ⟨s, hs, hr⟩ := (carterReachableHeightExact k q M q (run M t)).mp
    (carterAllRunsReachable k q M t)
  exact ⟨s, (carterTreeEnumerationExact k q s).mpr hs, hr,
    lt_of_lt_of_le (carterTreeSizeBound k s) (Nat.pow_le_pow_right (by decide) hs)⟩

theorem carterAcceptedWitnessSound : Targets.CarterAcceptedWitnessSound := by
  intro k q M t h
  unfold acceptedWitness at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  simpa only [decide_eq_true_eq, accepts] using List.find?_some h

theorem carterAcceptedWitnessComplete : Targets.CarterAcceptedWitnessComplete := by
  intro k q M
  rw [carterLanguageEmptiness]
  constructor
  · intro h
    have hn := List.find?_eq_none.mp h
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, hrun, _⟩ := carterBoundedRunRepresentative k q M t
    apply hn s hs
    simpa only [decide_eq_true_eq, hrun, accepts] using ht
  · intro h
    apply List.find?_eq_none.mpr
    intro t _ ht
    exact h ⟨t, by simpa only [decide_eq_true_eq, accepts] using ht⟩

end LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof
