module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowStandardInstances

@[expose] public section

/-! New standard-instance consequences of the unchanged accepted full-language
substitution supplier. Exact target was independently compiled and frozen. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof

open GorbowSyntax GorbowStandardInstances

theorem literalInstantiation : Comparators.GorbowStandardInstances.LiteralInstantiation := by
  intro n φ t I v
  let σ : Fin (n + 1) → Term n := Fin.cases t Term.var
  have h := GorbowFormulaSubstitution.substituteFormula_realize φ I v σ
  have he : (fun i => (σ i).realize I v) = Fin.cases (t.realize I v) v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he] at h
  exact h

theorem closedTermInterpretation : Comparators.GorbowStandardInstances.ClosedTermInterpretation := by
  intro n t I v
  have h := GorbowSubstitution.substitute_realize I v (Fin.elim0 : Fin 0 → Term n) t
  have he : (fun i : Fin 0 => (Fin.elim0 i : Term n).realize I v) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he] at h
  exact h

theorem numeralInstances : Comparators.GorbowStandardInstances.NumeralInstances := by
  intro n φ k I v
  simpa only [numeral_realize] using literalInstantiation n φ (Term.numeral k) I v

private theorem closedInstance (n : Nat) (φ : Formula (n + 1)) (t : Term 0)
    (I : Interpretation) (v : Fin n → Nat) :
    (instantiate φ (closedTermInContext n t)).realize I v ↔
      φ.realize I (Fin.cases (t.realize I Fin.elim0) v) := by
  have h := literalInstantiation n φ (closedTermInContext n t) I v
  rw [closedTermInterpretation n t I v] at h
  exact h

theorem fullClosedTermQuantifiers : Comparators.GorbowStandardInstances.FullClosedTermQuantifiers := by
  intro n φ I v
  constructor
  · constructor
    · intro h t
      exact (closedInstance n φ t I v).mpr (h (t.realize I Fin.elim0))
    · intro h x
      simpa only [numeral_realize] using
        (closedInstance n φ (Term.numeral x) I v).mp (h (Term.numeral x))
  · constructor
    · rintro ⟨x, hx⟩
      refine ⟨Term.numeral x, (closedInstance n φ (Term.numeral x) I v).mpr ?_⟩
      simpa only [numeral_realize] using hx
    · rintro ⟨t, ht⟩
      exact ⟨t.realize I Fin.elim0, (closedInstance n φ t I v).mp ht⟩

theorem arithmeticNumerals : Comparators.GorbowStandardInstances.ArithmeticNumerals := by
  intro n k
  induction k with
  | zero => exact ArithmeticTerm.zero
  | succ k ih => exact ArithmeticTerm.succ ih

theorem arithmeticClosedTermQuantifiers : Comparators.GorbowStandardInstances.ArithmeticClosedTermQuantifiers := by
  intro n φ I v
  constructor
  · constructor
    · intro h t ht
      exact (closedInstance n φ t I v).mpr (h (t.realize I Fin.elim0))
    · intro h x
      simpa only [numeral_realize] using
        (closedInstance n φ (Term.numeral x) I v).mp (h (Term.numeral x) (arithmeticNumerals 0 x))
  · constructor
    · rintro ⟨x, hx⟩
      refine ⟨Term.numeral x, arithmeticNumerals 0 x, (closedInstance n φ (Term.numeral x) I v).mpr ?_⟩
      simpa only [numeral_realize] using hx
    · rintro ⟨t, ht, hv⟩
      exact ⟨t.realize I Fin.elim0, (closedInstance n φ t I v).mp hv⟩

theorem gorbowStandardInstances : Comparators.GorbowStandardInstances.Target :=
  ⟨literalInstantiation, closedTermInterpretation, numeralInstances, fullClosedTermQuantifiers,
    arithmeticNumerals, arithmeticClosedTermQuantifiers⟩

end LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof
