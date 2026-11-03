module
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitContextSelectionCode.Targets

def ExactTypedSelection : Prop := ∀ Γ : List Ty,
  selectCode (Γ.map SyntaxCode.typeCode) = selectionCode (UnitElimination.select Γ)

def ExactRawSplit : Prop :=
  (∀ Γ : List Nat, selectCode Γ = none ↔ ∀ σ ∈ Γ, σ=0) ∧
  (∀ (Γ left right : List Nat) (σ : Nat),
    selectCode Γ = some (left,σ,right) ↔
      Γ = left++σ::right ∧ (∀ τ ∈ left, τ=0) ∧ σ≠0) ∧
  ∀ (Γ left right : List Nat) (σ : Nat), selectCode Γ = some (left,σ,right) →
    (left++right).length < Γ.length

def PrimitiveRecursiveSelection : Prop := Primrec selectCode
end LogicLineages.OrdinalComparison.Source.UnitContextSelectionCode.Targets
