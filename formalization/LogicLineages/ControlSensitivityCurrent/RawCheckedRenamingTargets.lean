module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open RawSourceDAG RawSourceDAG.CheckedRenaming

def TableExactness : Prop :=
  ∀ (Γ Θ : List Ty) (table : List Nat),
    tableGuard (Γ.map SyntaxCode.typeCode) (Θ.map SyntaxCode.typeCode) table = true ↔
      ∃ r : Renaming Γ Θ, Operations.renamingCode r = table

def TypedExactness : Prop :=
  ∀ (Γ Θ : List Ty) (τ : Ty) (r : Renaming Γ Θ) (d : Input Γ τ),
    rename (Θ.map SyntaxCode.typeCode) (Operations.renamingCode r) (encode ⟨Γ,τ,d⟩) =
      some (encode ⟨Θ,τ,ScopedDAG.renameInput r d⟩)

def SuccessReconstruction : Prop :=
  ∀ (target table : List Nat) (c out : Code), rename target table c = some out →
    ∃ (Γ Θ : List Ty) (τ : Ty) (r : Renaming Γ Θ) (d : Input Γ τ),
      encode ⟨Γ,τ,d⟩ = c ∧ Θ.map SyntaxCode.typeCode = target ∧
      Operations.renamingCode r = table ∧ out = encode ⟨Θ,τ,ScopedDAG.renameInput r d⟩ ∧
      decode out = some ⟨Θ,τ,ScopedDAG.renameInput r d⟩

def RejectionAndCounts : Prop :=
  (∀ (target table : List Nat) (c : Code), rename target table c = none ↔ guard target table c = false) ∧
  ∀ (target table : List Nat) (c out : Code), rename target table c = some out →
    valid out = true ∧ out.1 = target ∧ out.2.1.length = c.2.1.length ∧ out.2.2 = c.2.2

def Effective : Prop :=
  Computable (fun p : List Nat × List Nat × Code => rename p.1 p.2.1 p.2.2)

end LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingTargets
