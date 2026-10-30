module

public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormulaTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
open scoped BigOperators
universe u v

theorem finite_sum_term_evaluation : Targets.groupFiniteSumTermEvaluation.{u} := by
  intro G _ n m
  induction m with
  | zero =>
    intro f a
    simp [finiteSumTerm, GroupTerm.eval]
  | succ m ih =>
    intro f a
    simp only [finiteSumTerm, GroupTerm.eval, ih, Fin.sum_univ_succ]

private theorem root_term_evaluation (G : Type u) [AddCommGroup G] (p j n m : ℕ)
    (a : Fin n → G) (d : Fin m → G) (z : Fin 1 → G) (i : Fin m) :
    (ulmRootTerm p j n m i).eval (append (append a d) z) = p ^ j • d i := by
  simp only [ulmRootTerm, multiple_term_evaluation G ((n + m) + 1) (p ^ j),
    GroupTerm.eval, append, Fin.addCases_left, Fin.addCases_right]

private theorem combination_term_evaluation (G : Type u) [AddCommGroup G] (p j n m : ℕ)
    (a : Fin n → G) (d : Fin m → G) (z : Fin 1 → G) (r : Fin m → ZMod p) :
    (ulmCombinationTerm p j n m r).eval (append (append a d) z) =
      ∑ i, (r i).val • (p ^ j • d i) := by
  simp only [ulmCombinationTerm, finite_sum_term_evaluation G ((n + m) + 1) m,
    multiple_term_evaluation G ((n + m) + 1), root_term_evaluation]

theorem ulm_lower_matrix_realization : Targets.groupUlmLowerMatrixRealization.{u} := by
  intro p _ G _ j n m a d z
  classical
  let e := Fintype.equivFin (Fin m → ZMod p)
  simp only [ulmLowerMatrix, QF.Realize,
    finite_conjunction_realization G ((n + m) + 1) m,
    finite_conjunction_realization G ((n + m) + 1) (Fintype.card (Fin m → ZMod p)),
    multiple_term_evaluation G ((n + m) + 1) p,
    root_term_evaluation, GroupTerm.eval]
  constructor
  · rintro ⟨hsocle, hcoeff⟩
    refine ⟨hsocle, ?_⟩
    intro r hr
    have hh := hcoeff (e r)
    simpa only [e, Equiv.symm_apply_apply, if_neg hr, QF.Realize,
      multiple_term_evaluation G ((n + m) + 1), GroupTerm.eval,
      append, Fin.addCases_right, combination_term_evaluation] using hh
  · rintro ⟨hsocle, hcoeff⟩
    refine ⟨hsocle, ?_⟩
    intro k
    by_cases hk : (Fintype.equivFin (Fin m → ZMod p)).symm k = 0
    · simp only [if_pos hk, QF.Realize, not_false_eq_true]
    · simpa only [if_neg hk, QF.Realize, multiple_term_evaluation G ((n + m) + 1),
        GroupTerm.eval, append, Fin.addCases_right, combination_term_evaluation]
        using hcoeff ((Fintype.equivFin (Fin m → ZMod p)).symm k) hk

theorem ulm_lower_witness_formula : Targets.groupUlmLowerWitnessFormula.{u,v} := by
  intro p _ j n m
  constructor
  · exact Complexity.pi one_ne_zero {0} (fun _ => 1)
      (fun _ => .qf (ulmLowerMatrix p j n m)) (fun _ => 0)
      (fun _ => zero_lt_one) (fun _ => Complexity.qf .sigma _)
  · intro G _ a d
    change (∀ i : ({0} : Set ℕ), ∀ z : Fin 1 → G,
      (ulmLowerMatrix p j n m).Realize (append (append a d) z)) ↔ _
    constructor
    · intro h
      have hsocle := ((ulm_lower_matrix_realization p G j n m a d (fun _ => 0)).mp
        (h ⟨0, by simp⟩ (fun _ => 0))).1
      refine ⟨hsocle, ?_⟩
      intro r hr hmem
      rw [finite_filtration_multiple_image G p (j + 1)] at hmem
      obtain ⟨y, hy⟩ := hmem
      have hcoeff := ((ulm_lower_matrix_realization p G j n m a d (fun _ => y)).mp
        (h ⟨0, by simp⟩ (fun _ => y))).2 r hr
      exact hcoeff (by simpa only [nsmulAddMonoidHom_apply] using hy)
    · rintro ⟨hsocle, hcoeff⟩ i z
      apply (ulm_lower_matrix_realization p G j n m a d z).mpr
      refine ⟨hsocle, ?_⟩
      intro r hr heq
      apply hcoeff r hr
      rw [finite_filtration_multiple_image G p (j + 1)]
      exact ⟨z 0, heq⟩

theorem ulm_root_representatives : Targets.groupUlmRootRepresentatives.{u} := by
  intro p _ G _ j m
  classical
  let S : AddSubgroup G := finiteFiltration p j
  let q : pSocle p S →+ UlmLayer p S := QuotientAddGroup.mk' (successorSocleSubgroup p S)
  constructor
  · rintro ⟨d, hsocle, hcoeff⟩
    let x : Fin m → pSocle p S := fun i =>
      ⟨p ^ j • d i, ⟨by
        change p ^ j • d i ∈ finiteFiltration p j
        rw [finite_filtration_multiple_image G p j]
        exact ⟨d i, rfl⟩, hsocle i⟩⟩
    refine ⟨fun i => q (x i), (ulm_finite_independence p G j m x).mpr ?_⟩
    exact hcoeff
  · rintro ⟨v, hv⟩
    choose x hx using fun i : Fin m =>
      (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p S)) (v i)
    have hli : LinearIndependent (ZMod p) (fun i => q (x i)) := by
      have hfun : (fun i => q (x i)) = v := funext hx
      rw [hfun]
      exact hv
    have hcoeff := (ulm_finite_independence p G j m x).mp hli
    have hroots : ∀ i : Fin m, ∃ y : G, p ^ j • y = (x i : G) := by
      intro i
      have hi := (x i).property.1
      change (x i : G) ∈ finiteFiltration p j at hi
      rw [finite_filtration_multiple_image G p j] at hi
      simpa only [multipleImage, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply] using hi
    choose d hd using hroots
    refine ⟨d, ?_, ?_⟩
    · intro i
      rw [hd]
      exact (x i).property.2
    · intro r hr
      simpa only [hd] using hcoeff r hr

theorem ulm_lower_formula : Targets.groupUlmLowerFormula.{u,v} := by
  intro p _ j n m
  constructor
  · exact Complexity.sigma (by simp) {0} (fun _ => m)
      (fun _ => ulmLowerWitnessFormula p j n m) (fun _ => 1)
      (fun _ => one_lt_two) (fun _ => (ulm_lower_witness_formula.{u,v} p j n m).1)
  · intro G _ a
    change (∃ i : ({0} : Set ℕ), ∃ d : Fin m → G,
      (ulmLowerWitnessFormula p j n m).Realize (append a d)) ↔ _
    rw [← ulm_root_representatives p G j m]
    constructor
    · rintro ⟨i, d, hd⟩
      exact ⟨d, ((ulm_lower_witness_formula.{u,v} p j n m).2 G a d).mp hd⟩
    · rintro ⟨d, hd⟩
      exact ⟨⟨0, by simp⟩, d, ((ulm_lower_witness_formula.{u,v} p j n m).2 G a d).mpr hd⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
