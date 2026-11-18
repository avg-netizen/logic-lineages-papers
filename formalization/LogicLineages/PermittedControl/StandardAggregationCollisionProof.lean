module
public import LogicLineages.PermittedControl.StandardAggregationTargets
public import LogicLineages.PermittedControl.StandardFunctionalDetectorProof
public import LogicLineages.ControlSensitivityCurrent.CollisionNumericProof
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardAggregation.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open StandardFunctionalDetector.Proof
open SelectedAggregation
open ControlSensitivityCurrent

 theorem selectedGrowth : FullAddition.Targets.SourceGrowth Phi :=
  StandardSourceFacts.Proof.numericalGrowth.2.2

 theorem selectedInflation : ∀ n, n≤Phi n := fun n => (self_lt_Phi n).le

 theorem groundResult {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (t : OriginalTerm Γ .ground) :
    GroundResult Phi policy ρ t := ground_facts  policy t ρ

 theorem eraser_control {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ .ground) :
    groundValue Phi policy ρ (SourceCollisionCompletion.eraser a b)=
      PolicyCollision.g Phi (3*groundValue Phi policy ρ a+groundValue Phi policy ρ b+2) := by
  rw [eraser_value  policy ρ a b]
  exact ParametricCoefficientOne.Proof.genericCoefficientOne Phi
    Phi_strictMono (selectedInflation ) _

 theorem collision_values {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ .ground) :
    groundValue Phi policy ρ (SourceCollisionCompletion.detectorLeft a b)=
      PolicyCollision.leftValue Phi (groundValue Phi policy ρ a) (groundValue Phi policy ρ b) ∧
    groundValue Phi policy ρ (SourceCollisionCompletion.detectorRight a b)=
      PolicyCollision.rightValue Phi (groundValue Phi policy ρ a) (groundValue Phi policy ρ b) := by
  constructor <;>
    simp only [SourceCollisionCompletion.detectorLeft,SourceCollisionCompletion.detectorRight,
      eraser_control  policy ρ,PolicyCollision.leftValue,PolicyCollision.rightValue]

 theorem sixEraserCollision : StandardAggregation.SixEraserCollision := by
  intro Γ policy ρ a b
  have h := PolicyCollision.numeric_collision Phi (selectedGrowth )
    (groundValue Phi policy ρ a) (groundValue Phi policy ρ b)
  have hs := PolicyCollision.numeric_strict Phi (selectedGrowth )
    (groundValue Phi policy ρ a) (groundValue Phi policy ρ b)
  obtain ⟨hl,hr⟩ := collision_values  policy ρ a b
  refine ⟨groundResult  policy ρ _,groundResult  policy ρ _,?_,?_,?_⟩
  · simpa only [hl,hr] using h.1
  · simpa only [hl,hr] using h.2.1
  · simpa only [hl,hr] using hs
end LogicLineages.PermittedControl.StandardAggregation.Proof
