module

public import LogicLineages.ComputabilityKnowledge.Comparators.PolynomialComparison
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitProof
public import LogicLineages.ComputabilityKnowledge.CircuitComparisonProof

@[expose] public section

/-! External Codex continuation: composition of the checked polynomial and
finite shared-valuation comparison constructions. No MRDP premise is added. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialComparisonProof

open PositiveExpression PolynomialCircuit PolynomialComparison

private theorem circuit_wellFormed (p : Code) (hp : p.WellFormed) : (circuit p).WellFormed :=
  (PolynomialCircuitProof.compiledWellFormed p hp).2

theorem fixedInputs : Comparators.PolynomialComparison.FixedInputs := by
  intro p hp ρ
  exact (PolynomialCircuitProof.zeroIff p hp (CircuitComparison.finiteVal ρ)).trans
    (CircuitComparisonProof.fixedInputs (circuit p) (circuit_wellFormed p hp) ρ)

private theorem solvable_iff (p : Code) (hp : p.WellFormed) :
    HasPositiveRoot p ↔ CircuitComparison.Solvable (circuit p) := by
  constructor
  · rintro ⟨ρ,hρ⟩
    exact ⟨ρ,(PolynomialCircuitProof.zeroIff p hp (CircuitComparison.finiteVal ρ)).mp hρ⟩
  · rintro ⟨ρ,hρ⟩
    exact ⟨ρ,(PolynomialCircuitProof.zeroIff p hp (CircuitComparison.finiteVal ρ)).mpr hρ⟩

theorem equalityWitness : Comparators.PolynomialComparison.EqualityWitness := by
  intro p hp
  exact (solvable_iff p hp).trans
    (CircuitComparisonProof.equalityWitness (circuit p) (circuit_wellFormed p hp))

theorem strictReduction : Comparators.PolynomialComparison.StrictReduction := by
  intro p hp
  exact (not_congr (solvable_iff p hp)).trans
    (CircuitComparisonProof.strictReduction (circuit p) (circuit_wellFormed p hp))

theorem weakReduction : Comparators.PolynomialComparison.WeakReduction := by
  intro p hp
  exact (not_congr (solvable_iff p hp)).trans
    (CircuitComparisonProof.weakReduction (circuit p) (circuit_wellFormed p hp))

theorem alwaysOrdered : Comparators.PolynomialComparison.AlwaysOrdered := by
  intro p hp
  exact CircuitComparisonProof.alwaysOrdered (circuit p) (circuit_wellFormed p hp)

theorem depthBound : Comparators.PolynomialComparison.DepthBound := by
  intro p hp
  exact CircuitComparisonProof.depthBound (circuit p) (circuit_wellFormed p hp)

theorem variablesBounded : Comparators.PolynomialComparison.VariablesBounded := by
  intro p hp
  exact CircuitComparisonProof.variablesBounded (circuit p) (circuit_wellFormed p hp)

theorem polynomialComparison : Comparators.PolynomialComparison.Target :=
  ⟨fixedInputs,equalityWitness,strictReduction,weakReduction,alwaysOrdered,depthBound,variablesBounded⟩

end LogicLineages.ComputabilityKnowledge.PolynomialComparisonProof
