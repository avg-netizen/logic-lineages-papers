module
public import LogicLineages.ModelsAlgebra.Forests.FiniteIdealCoverTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteIdealCover.Proof

theorem finiteHost {α ι : Type} (R : α → α → Prop) (K : α → Prop)
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hjep : JEP R K) (a : α) (ha : K a) (g : ι → α)
    (hg : ∀ i, K (g i)) (S : Finset ι) :
    ∃ c, K c ∧ ∀ i ∈ S, R (g i) c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨a, ha, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨c, hc, hbound⟩ := ih
    obtain ⟨d, hd, hid, hcd⟩ := hjep (g i) c (hg i) hc
    refine ⟨d, hd, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjS
    · subst j
      exact hid
    · exact htrans (g j) c d (hbound j hjS) hcd

theorem finiteCoverCriterion : Targets.FiniteCoverCriterion := by
  classical
  intro α ι _ _ R K D hrefl htrans hcover hher hpieces
  constructor
  · intro hjep
    by_contra hproper
    have hmissing : ∀ i, ∃ x, K x ∧ ¬ D i x := by
      intro i
      by_contra hn
      apply hproper
      refine ⟨i, ?_⟩
      intro x hx
      by_contra hd
      exact hn ⟨x, hx, hd⟩
    let g : ι → α := fun i => Classical.choose (hmissing i)
    have hg : ∀ i, K (g i) := fun i => (Classical.choose_spec (hmissing i)).1
    have hnot : ∀ i, ¬ D i (g i) := fun i => (Classical.choose_spec (hmissing i)).2
    let i₀ : ι := Classical.choice inferInstance
    obtain ⟨c, hc, hbound⟩ := finiteHost R K hrefl htrans hjep (g i₀) (hg i₀) g hg
      (Finset.univ : Finset ι)
    obtain ⟨j, hj⟩ := (hcover c).mp hc
    exact hnot j (hher j (g j) c (hbound j (Finset.mem_univ j)) hj)
  · rintro ⟨i, hi⟩ a b ha hb
    obtain ⟨c, hc, hac, hbc⟩ := hpieces i a b (hi a ha) (hi b hb)
    exact ⟨c, (hcover c).mpr ⟨i, hc⟩, hac, hbc⟩

end LogicLineages.ModelsAlgebra.Forests.FiniteIdealCover.Proof
