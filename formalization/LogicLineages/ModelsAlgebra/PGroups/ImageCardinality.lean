module

public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityTargets
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

private theorem witnesses_of_embedding (G : Type u) [AddCommGroup G] (c m : ℕ)
    (e : Fin m ↪ Set.range (fun x : G => c • x)) :
    ∃ d : Fin m → G, Function.Injective (fun i => c • d i) := by
  classical
  choose d hd using fun i => (e i).property
  refine ⟨d, ?_⟩
  intro i j hij
  apply e.injective
  apply Subtype.ext
  exact (hd i).symm.trans (hij.trans (hd j))

theorem image_distinct_cardinality : Targets.groupImageDistinctCardinality.{u} := by
  intro G _ c m hfinite
  classical
  let R : Set G := Set.range (fun x : G => c • x)
  letI : Finite R := hfinite
  letI : Fintype R := Fintype.ofFinite R
  rw [Nat.card_eq_fintype_card]
  constructor
  · rintro ⟨d, hd⟩
    let f : Fin m → R := fun i => ⟨c • d i, ⟨d i, rfl⟩⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact hd (congrArg Subtype.val hij)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  · intro hcard
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin m) (β := R) (by simpa only [Fintype.card_fin] using hcard)
    exact witnesses_of_embedding G c m e

theorem image_bound_cardinality : Targets.groupImageBoundCardinality.{u} := by
  intro G _ c m
  classical
  let R : Set G := Set.range (fun x : G => c • x)
  constructor
  · intro h
    have hfinite : Finite R := by
      by_contra hnot
      letI : Infinite R := not_finite_iff_infinite.mp hnot
      let e : Fin (m + 1) ↪ R := Fin.valEmbedding.trans (Infinite.natEmbedding R)
      exact h (witnesses_of_embedding G c (m + 1) e)
    refine ⟨hfinite, ?_⟩
    have hnot : ¬ m + 1 ≤ Nat.card R := by
      intro hcard
      exact h ((image_distinct_cardinality G c (m + 1) hfinite).mpr hcard)
    exact Nat.le_of_lt_succ (lt_of_not_ge hnot)
  · rintro ⟨hfinite, hcard⟩ hwitnesses
    have hle := (image_distinct_cardinality G c (m + 1) hfinite).mp hwitnesses
    exact Nat.not_succ_le_self m (hle.trans hcard)

theorem bounded_multiple_image_formula : Targets.groupBoundedMultipleImageFormula.{u,v} := by
  intro c m
  constructor
  · exact Complexity.pi one_ne_zero {0} (fun _ => m + 1)
      (fun _ => .qf (.neg (distinctMultipleMatrix c 0 (m + 1)))) (fun _ => 0)
      (fun _ => zero_lt_one) (fun _ => Complexity.qf .sigma _)
  · intro G _
    change (∀ i : ({0} : Set ℕ), ∀ d : Fin (m + 1) → G,
      ¬ (distinctMultipleMatrix c 0 (m + 1)).Realize
        (append (Fin.elim0 : Fin 0 → G) d)) ↔ _
    rw [← image_bound_cardinality G c m]
    constructor
    · intro h
      rintro ⟨d, hd⟩
      exact h ⟨0, by simp⟩ d
        ((distinct_multiple_matrix_realization G c 0 (m + 1) Fin.elim0 d).mpr hd)
    · intro h i d hd
      exact h ⟨d, (distinct_multiple_matrix_realization G c 0 (m + 1) Fin.elim0 d).mp hd⟩

theorem exact_multiple_image_card_formula : Targets.groupExactMultipleImageCardFormula.{u,v} := by
  intro c m
  constructor
  · exact ⟨(distinct_multiples_formula.{u,v} c 0 m).1,
      (bounded_multiple_image_formula.{u,v} c m).1⟩
  · intro G _
    change ((distinctMultiples c 0 m).Realize (Fin.elim0 : Fin 0 → G) ∧
      (boundedMultipleImage c m).Realize (Fin.elim0 : Fin 0 → G)) ↔ _
    rw [(distinct_multiples_formula.{u,v} c 0 m).2 G Fin.elim0,
      (bounded_multiple_image_formula.{u,v} c m).2 G]
    constructor
    · rintro ⟨hwitnesses, hfinite, hupper⟩
      exact ⟨hfinite, Nat.le_antisymm hupper
        ((image_distinct_cardinality G c m hfinite).mp hwitnesses)⟩
    · rintro ⟨hfinite, hcard⟩
      exact ⟨(image_distinct_cardinality G c m hfinite).mpr hcard.ge, hfinite, hcard.le⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
