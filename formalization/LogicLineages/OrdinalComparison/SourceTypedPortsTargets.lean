module
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypedPortsTargets
open SourceTypedPorts SourceFreeOccurrences

def TypedVariableEnumeration : Prop := ∀ (Γ : List Ty) (σ : Ty) (v : Variable Γ σ), v ∈ enumerateVariables Γ σ

def TypedVariableIndex : Prop :=
  (∀ (Γ : List Ty) (σ : Ty) (v : Variable Γ σ), variableIndex v < Γ.length) ∧
  (∀ (Γ : List Ty) (v w : PackedVariable Γ), variableIndex v.2 = variableIndex w.2 → v = w)

def TypedAssignmentEnumeration : Prop := ∀ (Θ Λ : List Ty) (a : PortMap Θ Λ),
    a ∈ injectiveMaps Θ Λ ↔ (indices a).Nodup

def AssignmentRenamingCalibration : Prop := ∀ (Γ Θ Λ : List Ty) (a : PortMap Θ Λ),
  (∀ (σ : Ty) (v : Variable Γ σ), renameWith Γ a (shiftVariable Λ v) = shiftVariable Θ v) ∧
  (∀ (σ : Ty) (v : Variable Λ σ),
    variableIndex (renameWith Γ a (embedLeft Γ v)) = (indices a)[variableIndex v]?.getD 0)

def AssignmentLift : Prop := ∀ (Γ Θ Λ : List Ty) (σ : Ty) (a : PortMap Θ Λ),
    ((indices a).Nodup → (indices (liftMap σ a)).Nodup) ∧
    @renameWith Γ (σ :: Θ) (σ :: Λ) (liftMap σ a) = @Renaming.lift (Λ ++ Γ) (Θ ++ Γ) σ (@renameWith Γ Θ Λ a)

def FreshPortAvailability : Prop := ∀ (B : Nat) (P : List (Fin B × Ty)),
    (P.map Prod.fst).Nodup → P.length < B → ∃ i : Fin B, i ∉ P.map Prod.fst
end LogicLineages.OrdinalComparison.Source.SourceTypedPortsTargets
