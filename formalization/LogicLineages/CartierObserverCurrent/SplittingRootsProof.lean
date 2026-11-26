module
public import LogicLineages.CartierObserverCurrent.SplittingRootsTargets
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SplittingRoots

theorem finiteFieldAndRoots : Targets.FiniteFieldAndRoots := by
  intro d
  constructor
  · infer_instance
  · unfold Root
    infer_instance

theorem actualSplitting : Targets.ActualSplitting := by
  intro d
  exact Polynomial.SplittingField.splits _

private theorem constant_eval (d : Nat) : (splitPolynomial d).eval 0 = 1 := by
  simp [splitPolynomial, SourceBudget.denominator, Polynomial.map_prod,
    Polynomial.eval_prod]

private theorem polynomial_ne_zero (d : Nat) : splitPolynomial d ≠ 0 := by
  intro h
  have := constant_eval d
  rw [h, Polynomial.eval_zero] at this
  exact zero_ne_one this

theorem exactAllRoots : Targets.ExactAllRoots := by
  intro d z
  classical
  simpa [rootSet, Polynomial.IsRoot.def] using
    Polynomial.mem_roots (polynomial_ne_zero d) (a := z)

theorem nonzeroRoots : Targets.NonzeroRoots := by
  intro d z hz
  have h := (exactAllRoots d z.val).mp z.property
  rw [hz, constant_eval] at h
  exact one_ne_zero h

theorem frobeniusFixedPolynomial : Targets.FrobeniusFixedPolynomial := by
  intro d
  simp [splitPolynomial, SourceBudget.denominator, Polynomial.map_prod]

private theorem square_root (d : Nat) (z : Root d) : z.val ^ 2 ∈ rootSet d := by
  apply (exactAllRoots d _).mpr
  have h := Polynomial.eval_map_apply (frobenius (FieldAt d) 2)
    (p := splitPolynomial d) z.val
  rw [frobeniusFixedPolynomial d, (exactAllRoots d z.val).mp z.property, map_zero] at h
  exact h

theorem frobeniusRootPermutation : Targets.FrobeniusRootPermutation := by
  intro d
  classical
  letI : Finite (Root d) := (finiteFieldAndRoots d).2
  let f : Root d → Root d := fun z => ⟨z.val ^ 2, square_root d z⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact (frobenius (FieldAt d) 2).injective (congrArg Subtype.val h)
  exact ⟨Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩, fun _ => rfl⟩

theorem fixedFieldExactlyF2 : Targets.FixedFieldExactlyF2 := by
  intro d x
  constructor
  · intro hx
    have hz : x * (x - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_two, hx, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · refine ⟨0, ?_, ?_⟩
      · simpa using h.symm
      · intro a ha
        apply (algebraMap (ZMod 2) (FieldAt d)).injective
        simpa [h] using ha
    · have hx1 : x = 1 := sub_eq_zero.mp h
      refine ⟨1, ?_, ?_⟩
      · simpa using hx1.symm
      · intro a ha
        apply (algebraMap (ZMod 2) (FieldAt d)).injective
        simpa [hx1] using ha
  · rintro ⟨a, ha, _⟩
    rw [← ha, ← map_pow]
    congr 1
    fin_cases a <;> decide

#audit_namespace LogicLineages.CartierObserverCurrent.SplittingRoots
end LogicLineages.CartierObserverCurrent.SplittingRoots
