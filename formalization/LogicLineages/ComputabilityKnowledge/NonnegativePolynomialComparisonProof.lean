module

public import LogicLineages.ComputabilityKnowledge.Comparators.NonnegativePolynomialComparison
public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftProof
public import LogicLineages.ComputabilityKnowledge.PolynomialComparisonProof

@[expose] public section

/-! External Codex continuation: full well-formed nonnegative-code composition.
This proves the explicit construction, not the missing MRDP classification. -/
namespace LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparisonProof

open PositiveExpression PolynomialCircuit PolynomialDomainShift NonnegativePolynomialComparison
open CircuitComparison (finiteVal)

private theorem shift_valid (p : Code) (hp : p.WellFormed) : (shift p).WellFormed :=
  PolynomialDomainShiftProof.wellFormedPreserved p hp

theorem fixedInputs : Comparators.NonnegativePolynomialComparison.FixedInputs := by
  intro p hp ν
  have hf := PolynomialComparisonProof.fixedInputs (shift p) (shift_valid p hp) (toPositive ν)
  have hv := PolynomialDomainShiftProof.forwardEvaluation p ν
  constructor
  · intro h
    obtain ⟨τ,ha,he⟩ := hf.mp (hv.trans h)
    refine ⟨τ,?_,he⟩
    intro j
    exact ha j
  · rintro ⟨τ,ha,he⟩
    apply hv.symm.trans
    apply hf.mpr
    refine ⟨τ,?_,he⟩
    intro j
    exact ha j

theorem equalityWitness : Comparators.NonnegativePolynomialComparison.EqualityWitness := by
  intro p hp
  exact (PolynomialDomainShiftProof.rootEquivalence p hp).trans
    (PolynomialComparisonProof.equalityWitness (shift p) (shift_valid p hp))

theorem alwaysOrdered : Comparators.NonnegativePolynomialComparison.AlwaysOrdered := by
  intro p hp
  exact PolynomialComparisonProof.alwaysOrdered (shift p) (shift_valid p hp)

theorem rootCounterexamples : Comparators.NonnegativePolynomialComparison.RootCounterexamples := by
  intro p hp
  constructor
  · constructor
    · intro h
      obtain ⟨τ,he⟩ := (equalityWitness p hp).mp h
      refine ⟨τ,?_⟩
      intro hlt
      omega
    · rintro ⟨τ,hnot⟩
      have hle := alwaysOrdered p hp τ
      apply (equalityWitness p hp).mpr
      exact ⟨τ,by omega⟩
  · constructor
    · intro h
      obtain ⟨τ,he⟩ := (equalityWitness p hp).mp h
      refine ⟨τ,?_⟩
      change ¬ (lower p).eval (finiteVal τ) + 1 ≤ (upper p).eval (finiteVal τ)
      omega
    · rintro ⟨τ,hnot⟩
      change ¬ (lower p).eval (finiteVal τ) + 1 ≤ (upper p).eval (finiteVal τ) at hnot
      have hle := alwaysOrdered p hp τ
      exact (equalityWitness p hp).mpr ⟨τ,by omega⟩

theorem strictReduction : Comparators.NonnegativePolynomialComparison.StrictReduction := by
  intro p hp
  exact (not_congr (PolynomialDomainShiftProof.rootEquivalence p hp)).trans
    (PolynomialComparisonProof.strictReduction (shift p) (shift_valid p hp))

theorem weakReduction : Comparators.NonnegativePolynomialComparison.WeakReduction := by
  intro p hp
  exact (not_congr (PolynomialDomainShiftProof.rootEquivalence p hp)).trans
    (PolynomialComparisonProof.weakReduction (shift p) (shift_valid p hp))

theorem circuitContract : Comparators.NonnegativePolynomialComparison.CircuitContract := by
  intro p hp
  have hc := PolynomialCircuitProof.compiledWellFormed (shift p) (shift_valid p hp)
  have hf := PolynomialCircuitProof.freshOutputs (shift p) (shift_valid p hp)
  exact ⟨rfl,hc.2,hf.1,rfl⟩

theorem depthBound : Comparators.NonnegativePolynomialComparison.DepthBound := by
  intro p hp
  exact PolynomialComparisonProof.depthBound (shift p) (shift_valid p hp)

theorem variablesBounded : Comparators.NonnegativePolynomialComparison.VariablesBounded := by
  intro p hp
  exact PolynomialComparisonProof.variablesBounded (shift p) (shift_valid p hp)

theorem nonnegativePolynomialComparison : Comparators.NonnegativePolynomialComparison.Target :=
  ⟨fixedInputs,equalityWitness,rootCounterexamples,strictReduction,weakReduction,circuitContract,
    alwaysOrdered,depthBound,variablesBounded⟩

end LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparisonProof
