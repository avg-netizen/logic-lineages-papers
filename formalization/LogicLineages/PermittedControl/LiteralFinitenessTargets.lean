module
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentBoundTargets
public import LogicLineages.StandardControlCurrent.PolicyPartialDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAbstractionDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.LiteralFinitenessTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.LiteralPartialDomain
open StandardControlCurrent

def ActualLiteralPartialDomain : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    Domain Γ σ i t ↔ ∃ v, AdmissiblePartial.run p i t = some v

def ActualLiteralPartialUniqueBound : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    Domain Γ σ i t → ∃! v : OrdinalPartialVector Γ σ,
      AdmissiblePartial.run p i t = some v ∧
        ∀ j, ordinalLiteralNodes (v j) ≤ 6 * 3 ^ ordinalLiteralNodes t

def CoordinateCalibration : Prop := ∀ (p : Policy) (Γ : List Ty)
    (a b : OrdinalExpression Γ),
  PolicyPartial.mergeCoordinate p 4 (typedCode a) (typedCode b) =
    some (typedCode (AdmissiblePartial.three p .activeAdd a b .one)) ∧
  PolicyPartial.mergeCoordinate p 5 (typedCode a) (typedCode b) =
    some (typedCode (AdmissiblePartial.three p .activeExp (AdmissiblePartial.twice p a) b .one))

def PartialLiteralCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ : Ty)
    (i : Nat) (t : OrdinalExpression (σ::Γ)),
  PolicyPartial.run p σ.level i (typedCode t) =
    (AdmissiblePartial.run p i t).map (fun v => List.ofFn (fun j => typedCode (v j)))

def PartialPrograms : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat × Nat => PolicyPartial.mergeCoordinate p x.1 x.2.1 x.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List Nat =>
    PolicyPartial.mergeCode p x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  Computable (fun x : Nat × Nat × Nat => PolicyPartial.run p x.1 x.2.1 x.2.2)

def PartialsCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
  PolicyAbstraction.partialsCode p σ.level m (vectorCode h) =
    (AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i))).map
      (fun ps => List.ofFn (fun i => List.ofFn (fun j => typedCode (ps i j))))

def FactorCalibration : Prop := ∀ (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
  PolicyAbstraction.factorCode σ.level (vectorCode h) =
    2^(σ.level+1) * ((List.ofFn h).map ordinalPartialSize).sum

def DeltaLiteralCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
  PolicyAbstraction.abstractionCode p σ.level m (vectorCode h) =
    (AdmissibleAssignment.abstraction p h).map vectorCode

def DeltaPrograms : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat × List Nat => PolicyAbstraction.partialsCode p x.1 x.2.1 x.2.2) ∧
  Primrec (fun x : Nat × List Nat => PolicyAbstraction.factorCode x.1 x.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List (List Nat) × Nat =>
    PolicyAbstraction.coordinateCode p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List (List Nat) =>
    PolicyAbstraction.resultCode p x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat => PolicyAbstraction.abstractionCode p x.1 x.2.1 x.2.2)

/-- Supporting actual finite syntax and programs only, not selected-control grading or covariance. -/
def FullLiteralFiniteness : Prop :=
  ActualLiteralPartialDomain ∧ ActualLiteralPartialUniqueBound ∧
  CoordinateCalibration ∧ PartialLiteralCalibration ∧ PartialPrograms ∧
  PartialsCalibration ∧ FactorCalibration ∧ DeltaLiteralCalibration ∧ DeltaPrograms

end LogicLineages.PermittedControl.LiteralFinitenessTargets
