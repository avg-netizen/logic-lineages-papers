module
public import LogicLineages.StandardControlCurrent.PolicyAbstractionDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAbstractionTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

def PartialsCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
  PolicyAbstraction.partialsCode p σ.level m (vectorCode h) =
    (AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i))).map
      (fun ps => List.ofFn (fun i => List.ofFn (fun j => typedCode (ps i j))))

def FactorCalibration : Prop := ∀ (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
  PolicyAbstraction.factorCode σ.level (vectorCode h) =
    2^(σ.level+1) * ((List.ofFn h).map ordinalPartialSize).sum

def LiteralCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
  PolicyAbstraction.abstractionCode p σ.level m (vectorCode h) =
    (AdmissibleAssignment.abstraction p h).map vectorCode

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat × List Nat => PolicyAbstraction.partialsCode p x.1 x.2.1 x.2.2) ∧
  Primrec (fun x : Nat × List Nat => PolicyAbstraction.factorCode x.1 x.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List (List Nat) × Nat =>
    PolicyAbstraction.coordinateCode p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List (List Nat) =>
    PolicyAbstraction.resultCode p x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat => PolicyAbstraction.abstractionCode p x.1 x.2.1 x.2.2)

def Full : Prop := PartialsCalibration ∧ FactorCalibration ∧ LiteralCalibration ∧ Programs
end LogicLineages.StandardControlCurrent.PolicyAbstractionTargets
