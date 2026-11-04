module
public import LogicLineages.OrdinalComparison.ParametricLiteralWeakWrapperDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricLiteralWeakWrapper.Targets
open ParametricSourceEraser

def ExactAssignment : Prop := ∀ (Γ : List Ty) (t : OriginalTerm Γ .ground)
    (v : OrdinalVector Γ 0),
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v →
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (identityApply t)=
    some (fun _ => .collapse .one (.add three (v 0))) ∧
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (constantApply t)=
    some (fun _ => .collapse .one (.add five (v 0)))

def FiniteCoefficientCalibration : Prop := ∀ (G : Nat → Nat) (Γ : List Ty)
    (ν : OrdinalComponent Γ → Ordinal) (t : OriginalTerm Γ .ground) (x : Nat),
  Scalar G ν t x →
  Scalar G ν (identityApply t) (ParametricCoefficientOne.coefficientOne G (x+3)) ∧
  Scalar G ν (constantApply t) (ParametricCoefficientOne.coefficientOne G (x+5))

def ControlValueCalibration : Prop := ∀ (G : Nat → Nat),
  StrictMono G → (∀ n : Nat,n≤G n) →
  ∀ (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal)
    (t : OriginalTerm Γ .ground) (x : Nat), Scalar G ν t x →
  Scalar G ν (identityApply t) (G (x+5)+1) ∧
  Scalar G ν (constantApply t) (G (x+7)+1)
end LogicLineages.OrdinalComparison.Source.ParametricLiteralWeakWrapper.Targets
