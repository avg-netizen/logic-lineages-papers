module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorComparisonProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain AdmissibleAssignment
open SourceCollisionCompletion (rawScalar)

theorem equal_detector {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b : OriginalTerm Γ unary) (h : VectorEqual ρ a b) :
    rawScalar (valuation ρ) (left a b)=rawScalar (valuation ρ) (right a b) := by
  obtain ⟨h0,h1⟩ := (vector_equal_values ρ a b).mp h
  have hx : observedApp ρ a b (combine a a)=observedApp ρ a b (combine a b) := by
    apply observed_equal
    · simp only [combine_scalar,h0,h1]
    · simp only [combine_head,h1]
  have hy : observedApp ρ a b (combine b b)=observedApp ρ a b (combine b a) := by
    apply observed_equal
    · simp only [combine_scalar,h0,h1]
    · simp only [combine_head,h1]
  rw [left_value,right_value,hx,hy]

theorem scalar_diagonal_domination {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b : OriginalTerm Γ unary) (hh : value1 ρ a=value1 ρ b)
    (hne : value0 ρ a≠value0 ρ b) :
    (4*observedApp ρ a b (combine a b)<observedApp ρ a b (combine a a) ∧
      4*observedApp ρ a b (combine b a)<observedApp ρ a b (combine a a)) ∨
    (4*observedApp ρ a b (combine a b)<observedApp ρ a b (combine b b) ∧
      4*observedApp ρ a b (combine b a)<observedApp ρ a b (combine b b)) := by
  by_cases hlt : value0 ρ b<value0 ρ a
  · left
    constructor
    · apply app_tail_dominates
      · simp only [combine_head,hh]
      · apply combine_scalar_gap
        · simp only [hh]
        · omega
    · apply app_tail_dominates
      · simp only [combine_head,hh]
      · apply combine_scalar_gap
        · simp only [hh]
        · omega
  · right
    have hgt : value0 ρ a<value0 ρ b := by omega
    constructor
    · apply app_tail_dominates
      · simp only [combine_head,hh]
      · apply combine_scalar_gap
        · simp only [hh]
        · omega
    · apply app_tail_dominates
      · simp only [combine_head,hh]
      · apply combine_scalar_gap
        · simp only [hh]
        · omega
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
