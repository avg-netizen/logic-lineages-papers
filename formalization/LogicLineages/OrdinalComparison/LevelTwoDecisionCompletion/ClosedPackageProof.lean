module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixSemanticsProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixSyntaxProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open PolynomialGraphCompletion.ExpressionSupportProof

/-- One shared valuation supplies the actual graph and comparison row. -/
theorem package_matrix_congr (p : Pair.Package) (hp : PackageCertified p)
    (ν μ : Nat → Nat) (h : ∀ i ∈ p.2.1, ν i = μ i) :
    Pair.Matrix p ν ↔ Pair.Matrix p μ := by
  have hpositive : (∀ i < p.1.2, 0 < ν i) ↔ ∀ i < p.1.2, 0 < μ i := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    rw [h i (hp.2.2.1 i hi)]
  have hrows : RowsHold p.2.2.1 ν ↔ RowsHold p.2.2.1 μ :=
    rows_hold_congr _ ν μ (fun r hr i hi => h i ((hp.2.2.2.1 r hr).2 i hi))
  have hcmp := fun i hi => h i (hp.2.2.2.2.2 i hi)
  have hdomain := row_domain_congr p.2.2.2.1 ν μ hcmp
  have hvalue := row_value_congr p.2.2.2.1 ν μ hcmp
  simp only [Pair.Matrix,hpositive,hrows,hdomain,hvalue]

/-- Restore zeros only outside the certified original prefix. No word value
is introduced as an independent witness and no graph node is forced positive. -/
theorem package_closed_iff (p : Pair.Package) (hp : PackageCertified p) :
    Pair.Closed p ↔ ∃ ν : Nat → Nat, Pair.Matrix p ν := by
  unfold Pair.Closed
  rw [PairProof.existsPrefix_iff_frame]
  constructor
  · rintro ⟨ν,_,hν⟩
    exact ⟨ν,hν⟩
  · rintro ⟨ν,hν⟩
    let μ : Nat → Nat := fun i => if i ∈ p.2.1 then ν i else 0
    refine ⟨μ,?_,(package_matrix_congr p hp ν μ ?_).mp hν⟩
    · intro i hi
      simp [μ,hi]
    · intro i hi
      simp [μ,hi]

theorem exactClosedPackage : Targets.ExactClosedPackage := by
  intro p hp
  rw [package_closed_iff p hp]
  exact exists_congr (fun ν => (exactMatrixSemantics p ν).symm)

#print axioms package_matrix_congr
#print axioms package_closed_iff
#print axioms exactClosedPackage

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
