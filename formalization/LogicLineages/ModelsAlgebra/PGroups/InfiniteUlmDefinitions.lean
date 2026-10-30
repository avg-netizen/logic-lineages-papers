module

public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormulaDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranchesDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Every finite independent family size is realized in the actual Ulm quotient. -/
noncomputable def infiniteUlmFormula (p : ℕ) [Fact p.Prime] (j n : ℕ) : Formula n :=
  countableConjAll (fun _ : ℕ => 0) (fun m => ulmLowerFormula p j n m)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
