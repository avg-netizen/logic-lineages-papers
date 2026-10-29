module

public import LogicLineages.ComputabilityKnowledge.Comparators.PolynomialDomainShift
public import Mathlib.Tactic.Ring

@[expose] public section

/-! External Codex continuation for literal Xi−1 expansion and the exact
finite nonnegative/positive valuation correspondence. No MRDP supplier. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftProof

open PositiveExpression PolynomialCircuit PolynomialDomainShift

private theorem interpret_append (as bs : Monomials) :
    interpretTerms (as ++ bs) = interpretTerms as + interpretTerms bs := by
  induction as with
  | nil => simp [interpretTerms]
  | cons m ms ih => simp [interpretTerms,ih,add_assoc]

private theorem interpret_attach (ms : Monomials) (i : Nat) :
    interpretTerms (ms.map (attachVariable i)) = MvPolynomial.X i * interpretTerms ms := by
  induction ms with
  | nil => simp [interpretTerms]
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    simp only [List.map_cons,attachVariable,interpretTerms,variableProduct,ih]
    ring

private theorem interpret_negate (ms : Monomials) :
    interpretTerms (ms.map negateCoefficient) = -interpretTerms ms := by
  induction ms with
  | nil => simp [interpretTerms]
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    simp only [List.map_cons,negateCoefficient,interpretTerms,map_neg,ih]
    ring

private theorem expand_polynomial (vs : List Nat) (z : Int) :
    interpretTerms (expand (z,vs)) = MvPolynomial.C z *
      MvPolynomial.eval₂ MvPolynomial.C
        (fun i => (MvPolynomial.X i : MvPolynomial Nat Int) - 1) (variableProduct vs) := by
  induction vs with
  | nil => simp [expand,interpretTerms,variableProduct]
  | cons i vs ih =>
    change interpretTerms ((expand (z,vs)).map (attachVariable i) ++
      (expand (z,vs)).map negateCoefficient) = _
    rw [interpret_append,interpret_attach,interpret_negate,ih]
    simp only [variableProduct,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X]
    ring

private theorem shift_terms_polynomial (ms : Monomials) :
    interpretTerms (shiftTerms ms) = MvPolynomial.eval₂ MvPolynomial.C
      (fun i => (MvPolynomial.X i : MvPolynomial Nat Int) - 1) (interpretTerms ms) := by
  induction ms with
  | nil => simp [shiftTerms,interpretTerms]
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    change interpretTerms (expand (z,vs) ++ shiftTerms ms) = _
    simp only [interpret_append,expand_polynomial,ih,interpretTerms,MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C]

theorem substitutionIdentity : Comparators.PolynomialDomainShift.SubstitutionIdentity :=
  fun p => shift_terms_polynomial p.monomials

theorem arityPreserved : Comparators.PolynomialDomainShift.ArityPreserved := fun _ => rfl

private theorem expanded_variables (vs : List Nat) (z : Int) :
    ∀ m ∈ expand (z,vs), ∀ i ∈ m.2, i ∈ vs := by
  induction vs with
  | nil =>
    intro m hm i hi
    simp only [expand,List.foldr_nil,List.mem_singleton] at hm
    subst m
    cases hi
  | cons j vs ih =>
    intro m hm i hi
    change m ∈ (expand (z,vs)).map (attachVariable j) ++ (expand (z,vs)).map negateCoefficient at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨m',hm',rfl⟩ := List.mem_map.mp hm
      rcases List.mem_cons.mp hi with rfl | hi
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih m' hm' i hi)
    · obtain ⟨m',hm',rfl⟩ := List.mem_map.mp hm
      exact List.mem_cons_of_mem _ (ih m' hm' i hi)

theorem wellFormedPreserved : Comparators.PolynomialDomainShift.WellFormedPreserved := by
  intro p hp m hm i hi
  obtain ⟨original,horiginal,hexp⟩ := List.mem_flatMap.mp hm
  exact hp original horiginal i (expanded_variables original.2 original.1 m hexp i hi)

theorem valuationBijection : Comparators.PolynomialDomainShift.ValuationBijection := by
  intro n
  constructor
  · intro ν
    funext i
    simp [toNonnegative,toPositive]
  · intro ρ
    funext i
    apply Subtype.ext
    change (ρ i).val - 1 + 1 = (ρ i).val
    have := (ρ i).property
    omega

private theorem eval_shift (p : Code) (r : Nat → Int) :
    MvPolynomial.eval r (interpret (shift p)) =
      MvPolynomial.eval (fun i => r i - 1) (interpret p) := by
  change MvPolynomial.eval₂ (RingHom.id Int) r (interpret (shift p)) =
    MvPolynomial.eval₂ (RingHom.id Int) (fun i => r i - 1) (interpret p)
  rw [substitutionIdentity p]
  have hi (i : Nat) : MvPolynomial.eval₂ (RingHom.id Int) r
      ((MvPolynomial.X i : MvPolynomial Nat Int) - 1) = r i - 1 := by
    change MvPolynomial.eval r ((MvPolynomial.X i : MvPolynomial Nat Int) - 1) = _
    simp
  simpa only [hi] using (MvPolynomial.eval₂_assoc (RingHom.id Int) r
    (fun i => (MvPolynomial.X i : MvPolynomial Nat Int) - 1) (interpret p)).symm

theorem forwardEvaluation : Comparators.PolynomialDomainShift.ForwardEvaluation := by
  intro p ν
  unfold PolynomialComparison.evalAt evalNonnegative
  rw [eval_shift]
  apply congrArg (fun r : Nat → Int => MvPolynomial.eval r (interpret p))
  funext i
  by_cases hi : i < p.inputCount
  · simp [CircuitComparison.finiteVal,finiteNat,toPositive,shift,hi]
  · simp only [CircuitComparison.finiteVal,finiteNat,shift,dif_neg hi] <;> rfl

theorem reverseEvaluation : Comparators.PolynomialDomainShift.ReverseEvaluation := by
  intro p ρ
  have h := forwardEvaluation p (toNonnegative ρ)
  exact (congrArg (fun v : Fin p.inputCount → PosNat => PolynomialComparison.evalAt (shift p) v)
    ((valuationBijection p.inputCount).2 ρ)).symm.trans h

theorem rootEquivalence : Comparators.PolynomialDomainShift.RootEquivalence := by
  intro p _
  constructor
  · rintro ⟨ν,hν⟩
    exact ⟨toPositive ν,(forwardEvaluation p ν).trans hν⟩
  · rintro ⟨ρ,hρ⟩
    exact ⟨toNonnegative ρ,(reverseEvaluation p ρ).symm.trans hρ⟩

theorem polynomialDomainShift : Comparators.PolynomialDomainShift.Target :=
  ⟨substitutionIdentity,arityPreserved,wellFormedPreserved,valuationBijection,
    forwardEvaluation,reverseEvaluation,rootEquivalence⟩

end LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftProof
