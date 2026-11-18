module
public import LogicLineages.PermittedControl.StandardDomainCalibrationTargets
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDenotationProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardDomainCalibration.Proof
open OrdinalComparison Source

 theorem closed_value (t : OriginalDomain.ClosedExpression) :
    SelectedSourceDomain.closedValue Phi t=OriginalDomain.closedValue t :=
  ParametricSourceSuccessor.Proof.denote_phi _ t

 theorem closed_grade (i : Nat) (t : OriginalDomain.ClosedExpression) :
    SelectedSourceDomain.ClosedGrade Phi i t ↔ OriginalDomain.ClosedGrade i t := by
  constructor
  · intro h
    induction h with
    | one i => exact .one i
    | omega i hi => exact .omega i hi
    | add ha hb ia ib => exact .add ia ib
    | emul hi ha hb ia ib => exact .emul hi ia ib
    | collapse ha hb hn ia ib =>
      apply OriginalDomain.ClosedGrade.collapse ia ib
      simpa only [closed_value,SelectedSourceDomain.finiteValue,OriginalDomain.finiteValue] using hn
    | promote hi hh ih => exact .promote hi ih
  · intro h
    induction h with
    | one i => exact .one i
    | omega i hi => exact .omega i hi
    | add ha hb ia ib => exact .add ia ib
    | emul hi ha hb ia ib => exact .emul hi ia ib
    | collapse ha hb hn ia ib =>
      apply SelectedSourceDomain.ClosedGrade.collapse ia ib
      simpa only [closed_value,SelectedSourceDomain.finiteValue,OriginalDomain.finiteValue] using hn
    | promote hi hh ih => exact .promote hi ih

 def toOriginal {Γ} (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ) :
    OriginalDomain.AdmissibleSubstitution Γ where
  vector := ρ.vector
  graded := fun x j => (closed_grade _ _).mp (ρ.graded x j)
  bounded := by intro τ x j; simpa only [closed_value] using ρ.bounded x j

 def fromOriginal {Γ} (σ : OriginalDomain.AdmissibleSubstitution Γ) :
    SelectedSourceDomain.AdmissibleSubstitution Phi Γ where
  vector := σ.vector
  graded := fun x j => (closed_grade _ _).mpr (σ.graded x j)
  bounded := by intro τ x j; simpa only [closed_value] using σ.bounded x j

 def domainEquiv (Γ : List Ty) :
    SelectedSourceDomain.AdmissibleSubstitution Phi Γ ≃ OriginalDomain.AdmissibleSubstitution Γ where
  toFun := toOriginal
  invFun := fromOriginal
  left_inv := by intro ρ; cases ρ; rfl
  right_inv := by intro σ; cases σ; rfl

 theorem expressionCalibration : StandardDomainCalibrationTargets.ExpressionCalibration := by
  intro Γ ρ σ h
  have hv : SelectedSourceDomain.valuation Phi ρ=OriginalDomain.valuation σ := by
    funext c
    rcases c with ⟨τ,x,j⟩
    change SelectedSourceDomain.closedValue Phi (ρ.vector x j)=OriginalDomain.closedValue (σ.vector x j)
    rw [h τ x j,closed_value]
  refine ⟨hv,?_⟩
  intro t
  change ParametricSourceSuccessor.denoteWith Phi (SelectedSourceDomain.valuation Phi ρ) t=_
  rw [hv]
  exact ParametricSourceSuccessor.Proof.denote_phi _ t

 theorem guard (Γ : List Ty) (f g : OrdinalExpression Γ) :
    SelectedSourceDomain.CollapseNormPremise Phi f g ↔ OriginalDomain.CollapseNormPremise f g := by
  constructor
  · intro h σ
    have he := (expressionCalibration Γ (fromOriginal σ) σ (fun _ _ _ => rfl)).2
    simpa only [he,SelectedSourceDomain.finiteValue,OriginalDomain.finiteValue] using h (fromOriginal σ)
  · intro h ρ
    have he := (expressionCalibration Γ ρ (toOriginal ρ) (fun _ _ _ => rfl)).2
    simpa only [he,SelectedSourceDomain.finiteValue,OriginalDomain.finiteValue] using h (toOriginal ρ)

 theorem ambient (Γ : List Ty) (i : Nat) (t : OrdinalExpression Γ) :
    SelectedSourceDomain.AmbientGrade Phi Γ i t ↔ OriginalDomain.AmbientGrade Γ i t := by
  constructor
  · intro h
    induction h with
    | one i => exact .one i
    | omega i hi => exact .omega i hi
    | var x j => exact .var x j
    | add ha hb ia ib => exact .add ia ib
    | emul hi ha hb ia ib => exact .emul hi ia ib
    | collapse ha hb hn ia ib => exact .collapse ia ib ((guard _ _ _).mp hn)
    | promote hi hh ih => exact .promote hi ih
  · intro h
    induction h with
    | one i => exact .one i
    | omega i hi => exact .omega i hi
    | var x j => exact .var x j
    | add ha hb ia ib => exact .add ia ib
    | emul hi ha hb ia ib => exact .emul hi ia ib
    | collapse ha hb hn ia ib => exact .collapse ia ib ((guard _ _ _).mpr hn)
    | promote hi hh ih => exact .promote hi ih

 theorem head (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ::Γ)) :
    SelectedSourceDomain.HeadGrade Phi Γ σ i t ↔ OriginalDomain.HeadGrade Γ σ i t := by
  constructor
  · intro h
    induction h with
    | one i => exact .one i
    | omega i hi => exact .omega i hi
    | var x j => exact .var x j
    | add ha hb ia ib => exact .add ia ib
    | emul hi ha hb ia ib => exact .emul hi ia ib
    | collapse ha hb hn ia ib => exact .collapse ia ib ((guard _ _ _).mp hn)
    | promote hi hh hf ih => exact .promote hi ih hf
  · intro h
    induction h with
    | one i => exact .one i
    | omega i hi => exact .omega i hi
    | var x j => exact .var x j
    | add ha hb ia ib => exact .add ia ib
    | emul hi ha hb ia ib => exact .emul hi ia ib
    | collapse ha hb hn ia ib => exact .collapse ia ib ((guard _ _ _).mpr hn)
    | promote hi hh hf ih => exact .promote hi ih hf

 theorem assignmentCalibration : StandardDomainCalibrationTargets.AssignmentCalibration := by
  intro Γ ρ σ h policy τ a
  apply congrArg (fun f => (AdmissibleAssignment.assignment policy a).map f)
  funext v j
  exact (expressionCalibration Γ ρ σ h).2 (v j)

 theorem standardDomainCalibration : StandardDomainCalibrationTargets.StandardDomainCalibration :=
  ⟨⟨closed_value,closed_grade⟩,(fun Γ => ⟨domainEquiv Γ,fun _ _ _ _ => rfl⟩),
    expressionCalibration,⟨guard,ambient,head⟩,assignmentCalibration⟩
end LogicLineages.PermittedControl.StandardDomainCalibration.Proof
