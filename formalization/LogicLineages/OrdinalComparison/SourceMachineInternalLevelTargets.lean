module
public import LogicLineages.OrdinalComparison.SourceMachineInternalLevelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineInternalLevel.Targets
open SourceGroundBinderFragment SourceMachineRawValuations SourceClasses

def StructuralLevel : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  AllGround Γ → Fragment t → InternalLevelBound 1 t

def ActualAggregateLevel : Prop := ∀ b e : Nat,
  InternalLevelBound 1 (SourceMachineAggregateBridge.aggregate b e).1 ∧
  InternalLevelBound 1 (SourceMachineAggregateBridge.aggregate b e).2
end LogicLineages.OrdinalComparison.Source.SourceMachineInternalLevel.Targets
