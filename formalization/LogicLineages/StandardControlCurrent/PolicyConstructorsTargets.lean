module
public import LogicLineages.StandardControlCurrent.PolicyConstructorsDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyConstructorsTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax PolicyConstructors

def ConstantCalibration : Prop :=
  (∀ (p : Policy) (Γ : List Ty),
    some (onesCode Ty.ground.level) =
      (AdmissibleAssignment.assignment p (Term.zeroC : OriginalTerm Γ Ty.ground)).map vectorCode) ∧
  (∀ (p : Policy) (Γ : List Ty),
    some (onesCode (Ty.arrow Ty.ground Ty.ground).level) =
      (AdmissibleAssignment.assignment p (Term.succC : OriginalTerm Γ (.arrow .ground .ground))).map vectorCode) ∧
  (∀ (p : Policy) (Γ : List Ty) (τ : Ty),
    some (onesCode (Ty.caseType τ).level) =
      (AdmissibleAssignment.assignment p (Term.caseC τ : OriginalTerm Γ (Ty.caseType τ))).map vectorCode) ∧
  (∀ (p : Policy) (Γ : List Ty) (σ : Ty),
    recursorCode p σ.level (Ty.recType σ).level =
      (AdmissibleAssignment.assignment p (Term.recC σ : OriginalTerm Γ (Ty.recType σ))).map vectorCode)

def TailCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (n : Nat) (f g : OrdinalExpression Γ),
  boxTailCode p n (typedCode f) (typedCode g) = some (typedCode (AdmissibleAssignment.boxTail p n f g))

def ApplicationCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ τ : Ty)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level),
  PolicyConstructors.applicationCode p τ.level σ.level (vectorCode f) (vectorCode g) =
    some (vectorCode (AdmissibleAssignment.application p f g))

def Programs : Prop := Primrec onesCode ∧ ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat => recursorCode p x.1 x.2) ∧
  Computable (fun x : Nat × Nat × Nat => boxTailCode p x.1 x.2.1 x.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List Nat =>
    PolicyConstructors.applicationCode p x.1 x.2.1 x.2.2.1 x.2.2.2)

/-- Supporting literal constructors, not partial/abstraction/full assignment. -/
def FullPolicyConstructors : Prop := ConstantCalibration ∧ TailCalibration ∧ ApplicationCalibration ∧ Programs
end LogicLineages.StandardControlCurrent.PolicyConstructorsTargets
