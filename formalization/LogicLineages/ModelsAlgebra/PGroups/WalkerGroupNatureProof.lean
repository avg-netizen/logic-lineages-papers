module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerGroupNatureTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerTerminalProof
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_countable_successor : Targets.walkerCountableSuccessor := by
  intro ξ _
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType, Ordinal.card_add_one]
  have h : ξ.card ≤ Cardinal.aleph0 := by
    simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α := ξ.ToType))
  calc
    ξ.card + 1 ≤ Cardinal.aleph0 + Cardinal.aleph0 := add_le_add h Cardinal.one_le_aleph0
    _ = Cardinal.aleph0 := Cardinal.aleph0_add_aleph0

private theorem finite_stage_card (p : ℕ) (hp : 0 < p) (parent : WalkerParentSequence) (n : ℕ) :
    Nat.card (walkerFinitePresentation p parent n).Carrier = p^n := by
  let E := Equiv.ofBijective (walkerFiniteDigitSum p parent n)
    (walker_finite_tree_unique_digits p hp parent n)
  rw [← Nat.card_congr E, Nat.card_fun]
  simp

private theorem finite_stage_exponent (p : ℕ) (hp : 0 < p) (parent : WalkerParentSequence)
    (n : ℕ) (x : (walkerFinitePresentation p parent n).Carrier) : p^n • x = 0 := by
  rw [← finite_stage_card p hp parent n]
  exact card_nsmul_eq_zero'

theorem walker_source_group_nature : Targets.walkerSourceGroupNature := by
  intro p _ ξ _
  have hp := (Fact.out : p.Prime)
  have hbasic : Countable (WalkerSourceGroup p ξ) ∧
      ∀ x : WalkerSourceGroup p ξ, ∃ n : ℕ, p^n • x = 0 := by
    rcases walker_source_realization p hp.pos ξ with ⟨n,e,he,f,_⟩ | ⟨e,he,f,_⟩
    · let parent := walkerFiniteOrdinalParent ξ n e he
      letI : Countable (walkerFinitePresentation p parent n).Carrier :=
        (walker_finite_tree_unique_digits p hp.pos parent n).2.countable
      refine ⟨f.symm.surjective.countable, ?_⟩
      intro x
      refine ⟨n, ?_⟩
      apply f.injective
      rw [map_nsmul, map_zero]
      exact finite_stage_exponent p hp.pos parent n (f x)
    · let parent := walkerInfiniteOrdinalParent ξ e he
      letI : Countable (WalkerSequentialGroup p parent) := walker_limit_countable p hp.pos parent
      refine ⟨f.symm.surjective.countable, ?_⟩
      intro x
      obtain ⟨n,d,hd⟩ := walker_limit_digits p hp.pos parent (f x)
      refine ⟨n, ?_⟩
      apply f.injective
      rw [map_nsmul, map_zero, ← hd, ← map_nsmul,
        finite_stage_exponent p hp.pos parent n, map_zero]
  refine ⟨hbasic.1, hbasic.2, ?_⟩
  exact zero_stage_reduced (WalkerSourceGroup p ξ) p hp.ne_zero (ξ+1)
    (walker_source_terminal p ξ).2

end LogicLineages.ModelsAlgebra.PGroups
