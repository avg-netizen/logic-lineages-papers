module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRenaming

def renameVector {Γ Δ : List Ty} (r : Renaming Γ Δ) {m : Nat}
    (v : OrdinalVector Γ m) : OrdinalVector Δ m :=
  fun j => ordinalExpressionRename r (v j)

def renamePartial {Γ Δ : List Ty} (r : Renaming Γ Δ) {σ : Ty}
    (v : OrdinalPartialVector Γ σ) : OrdinalPartialVector Δ σ :=
  fun j => ordinalExpressionRename r (v j)
end LogicLineages.OrdinalComparison.Source.SourceRenaming
