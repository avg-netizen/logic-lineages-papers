module
public import LogicLineages.PermittedControl.SelectedAggregationTargets
public import LogicLineages.PermittedControl.SelectedFunctionalDetectorProof
public import LogicLineages.ControlSensitivityCurrent.CollisionNumericProof
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedAggregation.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open SelectedFunctionalDetector.Proof
open ControlSensitivityCurrent

 theorem selectedGrowth (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) :
    FullAddition.Targets.SourceGrowth ctrl := by
  refine ⟨(selected_threshold_admissible ctrl K hc).2, ?_⟩
  rcases hc with ⟨rfl,hK⟩ | ⟨b,rfl,hK⟩
  · exact factorialControl_separation
  · exact nearControl_separation b

 theorem selectedInflation (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) :
    ∀ n, n≤ctrl n := by
  intro n
  exact (by have h := G_large n; omega : n≤G n).trans
    ((selected_threshold_admissible ctrl K hc).2 n)

 theorem groundResult {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (t : OriginalTerm Γ .ground) :
    GroundResult ctrl policy ρ t := ground_facts ctrl K hc policy t ρ

 theorem eraser_control {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ .ground) :
    groundValue ctrl policy ρ (SourceCollisionCompletion.eraser a b)=
      PolicyCollision.g ctrl (3*groundValue ctrl policy ρ a+groundValue ctrl policy ρ b+2) := by
  rw [eraser_value ctrl K hc policy ρ a b]
  exact ParametricCoefficientOne.Proof.genericCoefficientOne ctrl
    (selected_threshold_admissible ctrl K hc).1 (selectedInflation ctrl K hc) _

 theorem collision_values {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ .ground) :
    groundValue ctrl policy ρ (SourceCollisionCompletion.detectorLeft a b)=
      PolicyCollision.leftValue ctrl (groundValue ctrl policy ρ a) (groundValue ctrl policy ρ b) ∧
    groundValue ctrl policy ρ (SourceCollisionCompletion.detectorRight a b)=
      PolicyCollision.rightValue ctrl (groundValue ctrl policy ρ a) (groundValue ctrl policy ρ b) := by
  constructor <;>
    simp only [SourceCollisionCompletion.detectorLeft,SourceCollisionCompletion.detectorRight,
      eraser_control ctrl K hc policy ρ,PolicyCollision.leftValue,PolicyCollision.rightValue]

 theorem sixEraserCollision : SelectedAggregationTargets.SixEraserCollision := by
  intro ctrl K hc Γ policy ρ a b
  have h := PolicyCollision.numeric_collision ctrl (selectedGrowth ctrl K hc)
    (groundValue ctrl policy ρ a) (groundValue ctrl policy ρ b)
  have hs := PolicyCollision.numeric_strict ctrl (selectedGrowth ctrl K hc)
    (groundValue ctrl policy ρ a) (groundValue ctrl policy ρ b)
  obtain ⟨hl,hr⟩ := collision_values ctrl K hc policy ρ a b
  refine ⟨groundResult ctrl K hc policy ρ _,groundResult ctrl K hc policy ρ _,?_,?_,?_⟩
  · simpa only [hl,hr] using h.1
  · simpa only [hl,hr] using h.2.1
  · simpa only [hl,hr] using hs
end LogicLineages.PermittedControl.SelectedAggregation.Proof
