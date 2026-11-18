module
public import LogicLineages.StandardControlCurrent.PolicyPartialDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyPartialTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

def CoordinateCalibration : Prop := ∀ (p : Policy) (Γ : List Ty)
    (a b : OrdinalExpression Γ),
  PolicyPartial.mergeCoordinate p 4 (typedCode a) (typedCode b) =
    some (typedCode (AdmissiblePartial.three p .activeAdd a b .one)) ∧
  PolicyPartial.mergeCoordinate p 5 (typedCode a) (typedCode b) =
    some (typedCode (AdmissiblePartial.three p .activeExp (AdmissiblePartial.twice p a) b .one))

def LiteralCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ : Ty)
    (i : Nat) (t : OrdinalExpression (σ::Γ)),
  PolicyPartial.run p σ.level i (typedCode t) =
    (AdmissiblePartial.run p i t).map (fun v => List.ofFn (fun j => typedCode (v j)))

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat × Nat => PolicyPartial.mergeCoordinate p x.1 x.2.1 x.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List Nat =>
    PolicyPartial.mergeCode p x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  Computable (fun x : Nat × Nat × Nat => PolicyPartial.run p x.1 x.2.1 x.2.2)

def Full : Prop := CoordinateCalibration ∧ LiteralCalibration ∧ Programs
end LogicLineages.StandardControlCurrent.PolicyPartialTargets
