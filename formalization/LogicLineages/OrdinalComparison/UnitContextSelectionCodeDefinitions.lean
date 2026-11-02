module
public import LogicLineages.OrdinalComparison.SourceUnitEliminationDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitContextSelectionCode

abbrev Split := List Nat × Nat × List Nat

/-- Select exactly the first non-ground type code. Prefix and suffix retain
all occurrences and their original order; none means every entry is ground. -/
def selectCode : List Nat → Option Split
  | [] => none
  | σ::Γ => if σ=0 then (selectCode Γ).map (fun r => (0::r.1,r.2.1,r.2.2))
    else some ([],σ,Γ)

def selectionCode {Γ : List Ty} : UnitElimination.Selection Γ → Option Split
  | .ground _ => none
  | .found left right σ _ => some (left.map SyntaxCode.typeCode,SyntaxCode.typeCode σ,right.map SyntaxCode.typeCode)
end LogicLineages.OrdinalComparison.Source.UnitContextSelectionCode
