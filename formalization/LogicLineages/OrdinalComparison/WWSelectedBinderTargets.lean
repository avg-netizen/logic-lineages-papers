module
public import LogicLineages.OrdinalComparison.WWSelectedBinderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedBinder.Targets
open SourceTypedPorts

def Inverses : Prop := ∀ (left right : List Ty) (σ τ : Ty),
  (∀ x : Variable (left ++ σ :: right) τ,
    moveFromHead left right σ (moveToHead left right σ x) = x) ∧
  (∀ x : Variable (σ :: (left ++ right)) τ,
    moveToHead left right σ (moveFromHead left right σ x) = x)

def Indices : Prop := ∀ (left right : List Ty) (σ τ : Ty)
    (x : Variable (left ++ σ :: right) τ),
  variableIndex (moveToHead left right σ x) =
    if variableIndex x < left.length then variableIndex x + 1
    else if variableIndex x = left.length then 0 else variableIndex x

def Selected : Prop := ∀ (left right : List Ty) (σ : Ty),
  moveToHead left right σ (selected left right σ) = .here ∧
  moveFromHead left right σ .here = selected left right σ

def SourceRoundTrip : Prop := ∀ (left right : List Ty) (σ τ : Ty)
    (t : OriginalTerm (left ++ σ :: right) τ),
  (t.rename (moveToHead left right σ)).rename (moveFromHead left right σ) = t

def AssignmentNaturality : Prop := ∀ (left right : List Ty) (σ τ : Ty)
    (p : AdmissibleSum.Policy) (t : OriginalTerm (left ++ σ :: right) τ),
  AdmissibleAssignment.assignment p (t.rename (moveToHead left right σ)) =
    (AdmissibleAssignment.assignment p t).map (SourceRenaming.renameVector (moveToHead left right σ))

/-- Every coordinate keeps the same shared value, and the newly selected head
has exactly the old selected coordinate's value (in particular literal one). -/
def ValuationNaturality : Prop := ∀ (left right : List Ty) (σ : Ty)
    (ρ : OrdinalComponent (left ++ σ :: right) → Nat),
  (∀ c, transport left right σ ρ (ordinalComponentRename (moveToHead left right σ) c) = ρ c) ∧
  (∀ j : Fin (σ.level+1), transport left right σ ρ ⟨σ, .here, j⟩ = ρ ⟨σ, selected left right σ, j⟩)
end LogicLineages.OrdinalComparison.Source.SelectedBinder.Targets
