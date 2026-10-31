module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorHeadOrderProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorEqualityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain
open SourceCollisionCompletion (rawScalar g)

theorem head_diagonal_domination {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b : OriginalTerm Γ unary) (hne : value1 ρ a≠value1 ρ b) :
    (4*observedApp ρ a b (combine a b)<observedApp ρ a b (combine a a) ∧
     4*observedApp ρ a b (combine b a)<observedApp ρ a b (combine a a)) ∨
    (4*observedApp ρ a b (combine a b)<observedApp ρ a b (combine b b) ∧
     4*observedApp ρ a b (combine b a)<observedApp ρ a b (combine b b)) := by
  have hz := (payload_components ρ a b).2.2.1
  have hw := (payload_components ρ a b).2.2.2
  have hc (u v w : OriginalTerm Γ unary) (huv : value1 ρ u<value1 ρ v) :
      value1 ρ (combine u w)<value1 ρ (combine v w) := by
    rw [combine_head,combine_head]
    exact headCombine_strict_left (value1 ρ u) (value1 ρ v) (value1 ρ w)
      (values_facts ρ u).2.2.1 (values_facts ρ v).2.2.1 (values_facts ρ w).2.2.1 huv
  have hs (u v : OriginalTerm Γ unary) : value1 ρ (combine u v)=value1 ρ (combine v u) := by
    rw [combine_head,combine_head,headCombine_comm]
  rcases lt_or_gt_of_ne hne with hab | hba
  · right
    exact ⟨app_head_dominates ρ a b _ _ (hc a b b hab) hz,
      app_head_dominates ρ a b _ _ (by rw [hs b a]; exact hc a b b hab) hw⟩
  · left
    exact ⟨app_head_dominates ρ a b _ _ (by rw [hs a b]; exact hc b a a hba) hz,
      app_head_dominates ρ a b _ _ (hc b a a hba) hw⟩

theorem unequal_strict {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary)
    (hne : ¬VectorEqual ρ a b) :
    rawScalar (valuation ρ) (right a b)+2≤rawScalar (valuation ρ) (left a b) := by
  have hd :
      (4*observedApp ρ a b (combine a b)<observedApp ρ a b (combine a a) ∧
       4*observedApp ρ a b (combine b a)<observedApp ρ a b (combine a a)) ∨
      (4*observedApp ρ a b (combine a b)<observedApp ρ a b (combine b b) ∧
       4*observedApp ρ a b (combine b a)<observedApp ρ a b (combine b b)) := by
    by_cases hh : value1 ρ a=value1 ρ b
    · have hn : value0 ρ a≠value0 ρ b := by
        intro h
        exact hne ((vector_equal_values ρ a b).mpr ⟨h,hh⟩)
      exact scalar_diagonal_domination ρ a b hh hn
    · exact head_diagonal_domination ρ a b hh
  have hi : 3*observedApp ρ a b (combine a b)+observedApp ρ a b (combine b a)+2 <
      3*observedApp ρ a b (combine a a)+observedApp ρ a b (combine b b)+2 := by
    rcases hd with hd | hd <;> omega
  rw [right_value,left_value]
  have hg := SourceCollisionCompletion.Proof.g_four_lt _ _ hi
  have hp := SourceCollisionCompletion.Proof.g_positive
    (3*observedApp ρ a b (combine a b)+observedApp ρ a b (combine b a)+2)
  omega

theorem detector {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) : Detects ρ a b := by
  dsimp only [Detects]
  by_cases he : VectorEqual ρ a b
  · have hv := equal_detector ρ a b he
    exact ⟨hv.ge,⟨fun _ => he,fun _ => hv⟩,fun h => False.elim (h he)⟩
  · have hs := unequal_strict ρ a b he
    exact ⟨by omega,⟨fun h => by omega,fun h => False.elim (he h)⟩,fun _ => hs⟩

theorem fullFunctionalDetector : Targets.FullFunctionalDetector := by
  intro Γ a b ρ
  exact ⟨alignment Γ a b ρ,detector ρ a b⟩
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
