module
public import LogicLineages.OrdinalComparison.CollectedReachableTargets
public import LogicLineages.OrdinalComparison.CollectedAffineBandProof
public import LogicLineages.OrdinalComparison.CollectedNonlinearBandProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

mutual
  private theorem reachable_domain (F : CollectedPositiveNF) (hv : CollectedPositiveValid F) :
      1≤collectedOneInputThreshold F ∧
      ∀ rho A, (rho,A)∈collectedReachableTags F →
        Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero ∧
        CollectedPositiveValid A ∧ collectedPositiveSupport A=true ∧
        collectedAtomThreshold rho A≤collectedOneInputThreshold F := by
    cases F with
    | mk c b tags => exact nested_domain tags hv
  private theorem nested_domain (tags : CollectedPositiveTags) (hv : CollectedTagsValid tags) :
      1≤collectedTagsOneInputThreshold tags ∧
      ∀ rho A, (rho,A)∈collectedNestedTags tags →
        Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero ∧
        CollectedPositiveValid A ∧ collectedPositiveSupport A=true ∧
        collectedAtomThreshold rho A≤collectedTagsOneInputThreshold tags := by
    cases tags with
    | nil =>
      refine ⟨le_rfl,?_⟩
      intro rho A hm
      simp [collectedNestedTags] at hm
    | cons sigma B b rest =>
      have hB := reachable_domain B hv.2.2.1
      have hr := nested_domain rest hv.2.2.2.2.2.2
      have htail : collectedTagsOneInputThreshold rest≤collectedTagsOneInputThreshold (.cons sigma B b rest) :=
        (le_max_right _ _).trans (le_max_right _ _)
      have harg : collectedOneInputThreshold B≤collectedTagsOneInputThreshold (.cons sigma B b rest) :=
        (le_max_left _ _).trans (le_max_right _ _)
      refine ⟨hr.1.trans htail,?_⟩
      intro rho A hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        exact ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,le_max_left _ _⟩
      · rcases List.mem_append.mp hm with hm | hm
        · have hd := hB.2 rho A hm
          exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.trans harg⟩
        · have hd := hr.2 rho A hm
          exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.trans htail⟩
end

theorem collectedReachableTagDomain : Targets.CollectedReachableTagDomain := reachable_domain

theorem collectedAtomInputRegime : Targets.CollectedAtomInputRegime := by
  intro rho c b tags hl he hv ho x hx
  dsimp only
  cases tags with
  | nil =>
    have hb : b≠0 := by
      simpa only [collectedPositiveSupport,collectedTagsSupport,Bool.or_false,bne_iff_ne] using ho
    have hband := (collectedAffineInputBand rho c b hl he (Nat.pos_of_ne_zero hb)).2 x hx
    exact ⟨fun _ => hband,fun h => False.elim (h rfl),Or.inl hband⟩
  | cons sigma A a rest =>
    have hn : CollectedPositiveTags.cons sigma A a rest≠.nil := by intro h; cases h
    have hband := (collectedNonlinearInputBand rho c b (.cons sigma A a rest) hl he hv hn).2 x hx
    exact ⟨fun h => False.elim (hn h),fun _ => ⟨hband.2.1,hband.1⟩,Or.inr ⟨hband.2.1,hband.1⟩⟩

end LogicLineages.OrdinalComparison
