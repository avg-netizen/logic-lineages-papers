module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Source fixed-limit head, on a faithful finite normal-notation index. -/
noncomputable def actualProfileHead (rho : NONote) (n : Nat) : Nat :=
  actualCollapse (rho.1.repr + (n : Ordinal))

/-- Executable closed notation for the added omega head in the reserve compiler. -/
def profileOmegaNote : NONote := ⟨ONote.oadd 1 1 0, inferInstance⟩

end LogicLineages.OrdinalComparison
