module

public import LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithmDefinitions
public import LogicLineages.ModelsAlgebra.Differential.ConstrainedDefinitions

@[expose] public section

/-! Full source cor:algorithmone comparison on faithful finite rational input
data. Genuine Computable realization plus semantic correctness is required. An arbitrary
classical Decidable instance or an assumed division oracle does not meet it.
-/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def orderOneAlgorithmInputCoverage : Prop :=
  ∀ (p : BivariatePolynomial) (q : Polynomial ℚ),
    ∃ (pc : OrderOneAlgorithm.Input) (qc : DensePolynomial.Code),
      OrderOneAlgorithm.inputValue pc = p ∧ DensePolynomial.value qc = q

def orderOneAlgorithmSpecialization : Prop :=
  ∀ pc, (OrderOneAlgorithm.inputValue pc).eval 0 =
    DensePolynomial.value (OrderOneAlgorithm.specialization pc)

def orderOneAlgorithmSearchCorrect : Prop :=
  ∀ (pc : OrderOneAlgorithm.Input) (qc : DensePolynomial.Code) (answer : Bool),
    Irreducible (OrderOneAlgorithm.inputValue pc) →
    0 < (OrderOneAlgorithm.inputValue pc).natDegree →
    DensePolynomial.value qc ≠ 0 →
    answer ∈ OrderOneAlgorithm.search pc qc →
    (answer = true ↔
      ConstrainedOrderOne.{u} (OrderOneAlgorithm.inputValue pc) (DensePolynomial.value qc))

def orderOneAlgorithmSearchTotal : Prop :=
  ∀ pc qc, (OrderOneAlgorithm.search pc qc).Dom

def orderOneAlgorithmSearchPartialRecursive : Prop := Partrec₂ OrderOneAlgorithm.search

/-- Complete source decidability on the source-valid input slice, with actual
realization of the literal search. The existential function must have a genuine
Mathlib Computable proof; no effective-polynomial-division supplier is assumed. -/
def orderOneAlgorithmComputableRealization : Prop :=
  ∃ f : OrderOneAlgorithm.Input → DensePolynomial.Code → Bool,
    Computable₂ f ∧ (∀ pc qc, f pc qc ∈ OrderOneAlgorithm.search pc qc) ∧
    (∀ pc qc, Irreducible (OrderOneAlgorithm.inputValue pc) →
      0 < (OrderOneAlgorithm.inputValue pc).natDegree → DensePolynomial.value qc ≠ 0 →
      (f pc qc = true ↔ ConstrainedOrderOne.{u}
        (OrderOneAlgorithm.inputValue pc) (DensePolynomial.value qc)))

end LogicLineages.ModelsAlgebra.Differential.Targets
