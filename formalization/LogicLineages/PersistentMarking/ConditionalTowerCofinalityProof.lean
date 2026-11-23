module

public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityTargets

public section

namespace LogicLineages.PersistentMarking.ConditionalTowerCofinality

universe u v

theorem conditionalTowerIncreasing : ConditionalTowerIncreasing.{u,v} := by
  intro I O _ _ D h
  have amono : StrictMono D.a := strictMono_nat_of_lt_succ h.increasing
  intro n m hnm
  exact (h.characterization (D.a m)).2.1 (D.a n) (amono hnm)
    (lt_of_le_of_lt (h.normBound n) (h.criticalAboveOne _ (h.characterization (D.a m)).1))

theorem conditionalTowerSupremum : ConditionalTowerSupremum.{u,v} := by
  intro I O _ _ D h θ hθ
  have amono : StrictMono D.a := strictMono_nat_of_lt_succ h.increasing
  have mono : StrictMono (fun n => D.psi (D.a n)) := conditionalTowerIncreasing I O D h
  have critθ : D.critical θ :=
    h.criticalSup _ mono (fun n => (h.characterization (D.a n)).1) θ hθ
  have upper : ∀ n, D.psi (D.a n) ≤ θ := fun n => hθ.1 ⟨n,rfl⟩
  have clause : ∀ η, η < D.endpoint → D.norm η < θ → D.psi η < θ := by
    intro η hη hnorm
    obtain ⟨c,⟨n,rfl⟩,hn⟩ := (lt_isLUB_iff hθ).1 hnorm
    obtain ⟨k,hk⟩ := h.cofinal η hη
    have h1 : η < D.a (max n k) := lt_of_lt_of_le hk (amono.monotone (le_max_right n k))
    have h2 : D.norm η < D.psi (D.a (max n k)) :=
      lt_of_lt_of_le hn (mono.monotone (le_max_left n k))
    exact lt_of_lt_of_le ((h.characterization (D.a (max n k))).2.1 η h1 h2) (upper _)
  have le1 : D.psi D.endpoint ≤ θ := (h.characterization D.endpoint).2.2 θ critθ clause
  have le2 : θ ≤ D.psi D.endpoint := by
    apply hθ.2
    rintro _ ⟨n,rfl⟩
    exact le_of_lt ((h.characterization D.endpoint).2.1 (D.a n) (h.below n)
      (lt_of_le_of_lt (h.normBound n)
        (h.criticalAboveOne _ (h.characterization D.endpoint).1)))
  exact le_antisymm le2 le1

theorem conditionalTowerCofinality : ConditionalTowerCofinality.{u,v} := by
  intro I O _ _ D BH h endpoint θ hθ
  have sup := conditionalTowerSupremum I O D h θ hθ
  exact ⟨sup,sup.trans endpoint⟩

#print axioms conditionalTowerIncreasing
#print axioms conditionalTowerSupremum
#print axioms conditionalTowerCofinality
end LogicLineages.PersistentMarking.ConditionalTowerCofinality
