module
public import LogicLineages.PermittedControl.NakedDeltaProgramDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.NakedDeltaProgramTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
open StandardControlCurrent

def LiteralCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
  NakedDeltaProgram.deltaCode p σ.level m (vectorCode h) =
    (LiteralCovariance.delta p h).map vectorCode

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat × List Nat × List (List Nat) × Nat =>
    NakedDeltaProgram.coordinateCode p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat × List (List Nat) =>
    NakedDeltaProgram.resultCode p x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  Computable (fun x : Nat × Nat × List Nat =>
    NakedDeltaProgram.deltaCode p x.1 x.2.1 x.2.2)

def FullNakedDeltaProgram : Prop := LiteralCalibration ∧ Programs

end LogicLineages.PermittedControl.NakedDeltaProgramTargets
