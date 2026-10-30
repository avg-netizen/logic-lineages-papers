module

public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivisionDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

open BoundedPolynomialDivision

def boundedDivisionInputCoverage : Prop := ∀ n (p q : MvPolynomial (Fin n) ℚ),
  ∃ B pc qc, 2 ≤ B ∧ BoxPolynomialCode.value n B pc = p ∧ BoxPolynomialCode.value n B qc = q

def boundedDivisionSearchCorrect : Prop := ∀ n B, 2 ≤ B → ∀ pc qc answer,
  answer ∈ search (n, B, pc, qc) →
    (answer = true ↔ BoxPolynomialCode.value n B pc ∣ BoxPolynomialCode.value n B qc)

def boundedDivisionSearchTotal : Prop := ∀ t : Input, (search t).Dom

def boundedDivisionSearchPartialRecursive : Prop := Partrec search

def boundedDivisionComputableRealization : Prop :=
  ∃ f : Input → Bool, Computable f ∧ (∀ t, f t ∈ search t) ∧
    ∀ n B, 2 ≤ B → ∀ pc qc,
      f (n, B, pc, qc) = true ↔ BoxPolynomialCode.value n B pc ∣ BoxPolynomialCode.value n B qc

end LogicLineages.ModelsAlgebra.Differential.Targets
