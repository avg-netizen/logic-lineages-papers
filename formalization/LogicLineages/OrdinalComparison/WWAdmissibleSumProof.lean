module
public import LogicLineages.OrdinalComparison.WWAdmissibleSumTargets
public import LogicLineages.OrdinalComparison.WWGeneratedGradeDefinitions
public import Mathlib.SetTheory.Ordinal.Principal
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem omega_coeff_lt (a e : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 a e < Ordinal.omega0 := by
  by_cases he : e ∈ (Ordinal.CNF Ordinal.omega0 a).map Prod.fst
  · obtain ⟨⟨e, c⟩, hm, rfl⟩ := List.mem_map.mp he
    rw [Ordinal.CNF.coeff_of_mem_CNF hm]
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hm
  · rw [Ordinal.CNF.coeff_of_notMem_CNF he]
    exact Ordinal.omega0_pos

private theorem naturalSum_coeff (a b : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalSum a b) =
      Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b := by
  apply Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0
  intro e
  exact Ordinal.isPrincipal_add_omega0 (omega_coeff_lt a e) (omega_coeff_lt b e)

private theorem naturalSum_assoc (a b c : Ordinal) :
    ordinalNaturalSum (ordinalNaturalSum a b) c =
      ordinalNaturalSum a (ordinalNaturalSum b c) := by
  unfold ordinalNaturalSum
  rw [show Ordinal.CNF.coeff Ordinal.omega0
      (Ordinal.CNF.eval Ordinal.omega0
        (Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b)) =
      Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b from
        naturalSum_coeff a b]
  rw [show Ordinal.CNF.coeff Ordinal.omega0
      (Ordinal.CNF.eval Ordinal.omega0
        (Ordinal.CNF.coeff Ordinal.omega0 b + Ordinal.CNF.coeff Ordinal.omega0 c)) =
      Ordinal.CNF.coeff Ordinal.omega0 b + Ordinal.CNF.coeff Ordinal.omega0 c from
        naturalSum_coeff b c]
  rw [add_assoc]


private theorem naturalSum_zero (a : Ordinal) : ordinalNaturalSum a 0 = a := by
  simp [ordinalNaturalSum, Ordinal.CNF.coeff_zero_right]

private theorem zero_naturalSum (a : Ordinal) : ordinalNaturalSum 0 a = a := by
  simp [ordinalNaturalSum, Ordinal.CNF.coeff_zero_right]

/-- Actual natural ordinal sum of a list, not ordinal addition. -/
noncomputable def values (xs : List Ordinal) : Ordinal := xs.foldr ordinalNaturalSum 0

private theorem values_append (xs ys : List Ordinal) :
    values (xs ++ ys) = ordinalNaturalSum (values xs) (values ys) := by
  induction xs with
  | nil => exact (zero_naturalSum _).symm
  | cons a xs ih =>
    change ordinalNaturalSum a (values (xs ++ ys)) =
      ordinalNaturalSum (ordinalNaturalSum a (values xs)) (values ys)
    rw [ih, naturalSum_assoc]

private theorem castAdd_eq_castLE {n m : Nat} (i : Fin n) :
    Fin.castAdd m i = Fin.castLE (Nat.le_add_right n m) i := Fin.ext rfl

theorem expand_value {Γ : List Ty} {n : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (ρ : OrdinalComponent Γ → Ordinal) :
    denote ρ (expand s xs) = values ((List.ofFn xs).map (denote ρ)) := by
  induction s with
  | leaf => simp [expand, List.ofFn_succ, List.ofFn_zero, values, naturalSum_zero]
  | @join n m a b iha ihb =>
    rw [expand, denote, List.ofFn_add, List.map_append, values_append]
    rw [iha, ihb]
    simp only [castAdd_eq_castLE]

theorem actualAdmissibleSumSyntax : Targets.ActualAdmissibleSumSyntax := by
  intro Γ n s
  induction s with
  | leaf =>
    intro xs
    simp [expand, operands, List.ofFn_succ, List.ofFn_zero]
  | @join n m a b iha ihb =>
    intro xs
    have ha := iha (fun i => xs (Fin.castAdd m i))
    have hb := ihb (fun i => xs (Fin.natAdd n i))
    refine ⟨by omega, ?_, ?_⟩
    · rw [operands, ha.2.1, hb.2.1]
      exact List.ofFn_add.symm
    · rw [expand, ordinalLiteralNodes, List.ofFn_add, List.map_append, List.sum_append]
      simp only [castAdd_eq_castLE] at ha ⊢
      omega

theorem actualAdmissibleSumValue : Targets.ActualAdmissibleSumValue := by
  intro Γ n s t xs ρ
  rw [expand_value, expand_value]

/-- Useful composition interface: output value depends only on operand values,
not their trees. This is about a single sum, never an enclosing partial. -/
theorem expand_value_congr {Γ : List Ty} {n : Nat} (s t : Shape n)
    (xs ys : Fin n → OrdinalExpression Γ) (ρ : OrdinalComponent Γ → Ordinal)
    (h : ∀ i, denote ρ (xs i) = denote ρ (ys i)) :
    denote ρ (expand s xs) = denote ρ (expand t ys) := by
  rw [expand_value, expand_value]
  congr 1
  rw [List.map_ofFn, List.map_ofFn]
  congr 1
  funext i
  exact h i

/-- Structural generated-grade composition, with no ordinal norm assumption. -/
theorem expand_generated {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ)
    (h : ∀ j, GeneratedOrdinalGrade Γ i (xs j)) :
    GeneratedOrdinalGrade Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

end LogicLineages.OrdinalComparison.Source.AdmissibleSum
