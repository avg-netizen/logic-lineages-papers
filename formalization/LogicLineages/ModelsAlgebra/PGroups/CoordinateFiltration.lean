module

public import LogicLineages.ModelsAlgebra.PGroups.CoordinateFiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

private theorem filtration_roots (G : Type*) [AddCommGroup G] (p j : ℕ) (x : G) :
    x ∈ finiteFiltration p j ↔ ∃ y : G, p ^ j • y = x := by
  rw [finite_filtration_multiple_image G p j]
  rfl

theorem pi_finite_filtration : Targets.groupPiFiniteFiltration.{u,v} := by
  classical
  intro ι G _ p j x
  simp only [filtration_roots]
  constructor
  · rintro ⟨y, hy⟩ i
    exact ⟨y i, congrArg (fun z : ∀ i, G i => z i) hy⟩
  · intro h
    refine ⟨fun i => Classical.choose (h i), ?_⟩
    funext i
    exact Classical.choose_spec (h i)

theorem pi_finite_socle : Targets.groupPiFiniteSocle.{u,v} := by
  intro ι G _ p j x
  change (x ∈ finiteFiltration p j ∧ p • x = 0) ↔
    ∀ i, x i ∈ finiteFiltration p j ∧ p • x i = 0
  rw [pi_finite_filtration]
  constructor
  · rintro ⟨hx, hz⟩ i
    exact ⟨hx i, congrArg (fun z : ∀ i, G i => z i) hz⟩
  · intro h
    exact ⟨fun i => (h i).1, funext fun i => (h i).2⟩

theorem finsupp_finite_filtration : Targets.groupFinsuppFiniteFiltration.{u,v} := by
  classical
  intro ι G _ p j x
  simp only [filtration_roots]
  constructor
  · rintro ⟨y, hy⟩ i
    exact ⟨y i, congrArg (fun z : ι →₀ G => z i) hy⟩
  · intro h
    let root : G → G := fun a => if h0 : a = 0 then 0 else
      if ha : ∃ b : G, p ^ j • b = a then Classical.choose ha else 0
    have hzero : root 0 = 0 := by simp [root]
    have hroot (a : G) (ha : ∃ b : G, p ^ j • b = a) : p ^ j • root a = a := by
      by_cases h0 : a = 0
      · simp [root, h0]
      · simp only [root, dif_neg h0, dif_pos ha]
        exact Classical.choose_spec ha
    refine ⟨x.mapRange root hzero, ?_⟩
    apply Finsupp.ext
    intro i
    exact hroot (x i) (h i)

theorem finsupp_finite_socle : Targets.groupFinsuppFiniteSocle.{u,v} := by
  intro ι G _ p j x
  change (x ∈ finiteFiltration p j ∧ p • x = 0) ↔
    ∀ i, x i ∈ finiteFiltration p j ∧ p • x i = 0
  rw [finsupp_finite_filtration]
  constructor
  · rintro ⟨hx, hz⟩ i
    exact ⟨hx i, congrArg (fun z : ι →₀ G => z i) hz⟩
  · intro h
    exact ⟨fun i => (h i).1, Finsupp.ext fun i => (h i).2⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
