module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivariance
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison

def renamePacked {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (ρ : Renaming Γ Δ) (p : Packed Symbol arity Γ) : Packed Symbol arity Δ :=
  ⟨p.1,renameTerm p.2 ρ⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivariance
