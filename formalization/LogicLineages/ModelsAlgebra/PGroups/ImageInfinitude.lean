module

public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeTargets
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem multiple_term_evaluation : Targets.groupMultipleTermEvaluation.{u} := by
  intro G _ n c t a
  induction c with
  | zero => simp [multipleTerm, GroupTerm.eval]
  | succ c ih => simp only [multipleTerm, GroupTerm.eval, ih, succ_nsmul]

theorem finite_conjunction_realization : Targets.groupFiniteConjunctionRealization.{u} := by
  intro G _ n m
  induction m with
  | zero =>
    intro f a
    simp [finiteAnd, QF.Realize]
  | succ m ih =>
    intro f a
    change (f 0).Realize a ∧ (finiteAnd m (fun i => f i.succ)).Realize a ↔ _
    rw [ih]
    exact (Fin.forall_fin_succ (P := fun i => (f i).Realize a)).symm

theorem distinct_multiple_matrix_realization : Targets.groupDistinctMultipleMatrixRealization.{u} := by
  intro G _ c n m a d
  unfold distinctMultipleMatrix
  simp only [finite_conjunction_realization G (n + m) m]
  constructor
  · intro h i j hij
    by_contra hne
    have hdistinct := h i j
    simp only [if_neg hne, QF.Realize, multiple_term_evaluation G (n + m) c, GroupTerm.eval,
      append, Fin.addCases_right] at hdistinct
    exact hdistinct hij
  · intro h i j
    by_cases hij : i = j
    · simp [hij, QF.Realize]
    · simp only [if_neg hij, QF.Realize, multiple_term_evaluation G (n + m) c, GroupTerm.eval,
        append, Fin.addCases_right]
      exact fun heq => hij (h heq)

theorem distinct_multiples_formula : Targets.groupDistinctMultiplesFormula.{u,v} := by
  intro c n m
  constructor
  · exact Complexity.sigma one_ne_zero {0} (fun _ => m)
      (fun _ => .qf (distinctMultipleMatrix c n m)) (fun _ => 0)
      (fun _ => zero_lt_one) (fun _ => Complexity.qf .pi _)
  · intro G _ a
    change (∃ i : ({0} : Set ℕ), ∃ d : Fin m → G,
      (distinctMultipleMatrix c n m).Realize (append a d)) ↔ _
    constructor
    · rintro ⟨i, d, hd⟩
      exact ⟨d, (distinct_multiple_matrix_realization G c n m a d).mp hd⟩
    · rintro ⟨d, hd⟩
      exact ⟨⟨0, by simp⟩, d, (distinct_multiple_matrix_realization G c n m a d).mpr hd⟩

private theorem image_infinite_iff_witnesses (G : Type u) [AddCommGroup G] (c : ℕ) :
    Set.Infinite (Set.range (fun x : G => c • x)) ↔
      ∀ m : ℕ, ∃ d : Fin m → G, Function.Injective (fun i => c • d i) := by
  classical
  let R : Set G := Set.range (fun x : G => c • x)
  constructor
  · intro hinfinite m
    let e : ℕ ↪ R := hinfinite.natEmbedding R
    choose d hd using fun i : Fin m => (e i.val).property
    refine ⟨d, ?_⟩
    intro i j hij
    apply Fin.val_injective
    apply e.injective
    apply Subtype.ext
    exact (hd i).symm.trans (hij.trans (hd j))
  · intro h hfinite
    letI : Fintype R := hfinite.fintype
    obtain ⟨d, hd⟩ := h (Fintype.card R + 1)
    let f : Fin (Fintype.card R + 1) → R := fun i => ⟨c • d i, ⟨d i, rfl⟩⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact hd (congrArg Subtype.val hij)
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hcard
    exact Nat.not_succ_le_self _ hcard

theorem infinite_multiple_image_formula : Targets.groupInfiniteMultipleImageFormula.{u,v} := by
  intro c
  constructor
  · exact Complexity.pi (by simp) Set.univ (fun _ => 0)
      (fun i => distinctMultiples c 0 i.val) (fun _ => 1)
      (fun _ => one_lt_two) (fun i => (distinct_multiples_formula.{u,v} c 0 i.val).1)
  · intro G _
    change (∀ i : (Set.univ : Set ℕ), ∀ a : Fin 0 → G,
      (distinctMultiples c 0 i.val).Realize (append (Fin.elim0 : Fin 0 → G) a)) ↔ _
    rw [image_infinite_iff_witnesses G c]
    constructor
    · intro h m
      exact ((distinct_multiples_formula.{u,v} c 0 m).2 G
        (append (Fin.elim0 : Fin 0 → G) Fin.elim0)).mp (h ⟨m, Set.mem_univ m⟩ Fin.elim0)
    · intro h i a
      exact ((distinct_multiples_formula.{u,v} c 0 i.val).2 G
        (append (Fin.elim0 : Fin 0 → G) a)).mpr (h i.val)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
