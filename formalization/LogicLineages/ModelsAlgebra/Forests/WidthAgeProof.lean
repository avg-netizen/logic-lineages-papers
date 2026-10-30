module

public import LogicLineages.ModelsAlgebra.Forests.WidthAgeTargets
public import LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof
public import LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof

/-! Actual width classes and their finite/countable ages. Finite chains pay
unboundedness, and finite induced restrictions pay the infinite carrier's width. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.WidthAgeProof

open AgeConstruction AgeCompletionProof AgeNecessaryProof WidthPositiveProof

private theorem width_embedding {α β : Type} [PartialOrder α] [PartialOrder β]
    {m : Nat} (e : α ↪o β) (h : WidthAtMost β m) : WidthAtMost α m := by
  classical
  intro s hs
  have hi : IsAntichain (· ≤ ·) (s.map e.toEmbedding : Set β) := by
    intro x hx y hy hne hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hne (congrArg e (hs.eq ha hb (e.le_iff_le.mp hxy)))
  simpa only [Finset.card_map] using h (s.map e.toEmbedding) hi

theorem widthClassHereditary : Targets.WidthClassHereditary := by
  rintro m F G hF ⟨e⟩
  exact width_embedding e hF

theorem widthClassNonempty : Targets.WidthClassNonempty := by
  intro m
  let F : FiniteOrderForest := {
    Carrier := Fin 0
    carrierFintype := inferInstance
    carrierPartialOrder := inferInstance
    forest := by intro x; exact Fin.elim0 x }
  refine ⟨F, ?_⟩
  intro s _
  have he : s = ∅ := Finset.eq_empty_of_forall_notMem (fun x => Fin.elim0 x)
  simp [he]

theorem widthClassUnbounded : Targets.WidthClassUnbounded := by
  intro m hm n
  let F : FiniteOrderForest := {
    Carrier := Fin (n + 1)
    carrierFintype := inferInstance
    carrierPartialOrder := inferInstance
    forest := fun {_ _ _} _ _ => le_total _ _ }
  refine ⟨F, ?_, ?_⟩
  · intro s hs
    have hc : s.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      exact hs.subsingleton hx hy)
    exact hc.trans hm
  · change n < Fintype.card (Fin (n + 1))
    simp

theorem realizedWidthAgeWidth : Targets.RealizedWidthAgeWidth := by
  classical
  intro m A hAge s hs
  let F : FiniteOrderForest := {
    Carrier := {x : A.Carrier // x ∈ s}
    carrierFintype := inferInstance
    carrierPartialOrder := inferInstance
    forest := fun {_ _ _} hx hy => A.forest hx hy }
  have hF : WidthAtMost F.Carrier m :=
    (hAge F).mpr ⟨OrderEmbedding.subtype (fun x => x ∈ s)⟩
  have hanti : IsAntichain (· ≤ ·) ((Finset.univ : Finset F.Carrier) : Set F.Carrier) := by
    intro x _ y _ hne hxy
    exact hne (Subtype.ext (hs.eq x.property y.property hxy))
  have hb := hF Finset.univ hanti
  change Fintype.card {x : A.Carrier // x ∈ s} ≤ m at hb
  simpa only [Fintype.card_coe] using hb

theorem widthAgeClassification : Targets.WidthAgeClassification := by
  intro m
  have he := fullForestAgeRealization (WidthClass m) (widthClassNonempty m)
    (widthClassHereditary m)
  constructor
  · intro h
    have hj : WidthHasJEP m := he.mp h
    by_cases hm : m = 0
    · omega
    · exact (fullWidthJEPClassification m (by omega)).mp hj
  · intro hm
    exact he.mpr (widthAtMostThreeHasJEP m hm)

theorem smallWidthCountablyInfiniteAge : Targets.SmallWidthCountablyInfiniteAge := by
  intro m hpos hm
  obtain ⟨A, hA, hInf⟩ := unboundedForestAgeRealization (WidthClass m)
    (widthClassNonempty m) (widthClassHereditary m)
    (widthAtMostThreeHasJEP m hm) (widthClassUnbounded m hpos)
  exact ⟨A, realizedWidthAgeWidth m A hA, hA, hInf⟩

end LogicLineages.ModelsAlgebra.Forests.WidthAgeProof
