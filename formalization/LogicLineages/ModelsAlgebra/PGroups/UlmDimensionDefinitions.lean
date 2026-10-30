module

public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormulaDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityDefinitions

@[expose] public section

/-! Actual upper and exact finite Ulm dimension descriptions. The semantic
comparators use Cardinal-valued Module.rank, never finrank (which is zero
for infinite-dimensional spaces). -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

noncomputable def ulmUpperFormula (p : ℕ) [Fact p.Prime] (j n m : ℕ) : Formula n :=
  (ulmLowerFormula p j n (m + 1)).dual

noncomputable def ulmExactFormula (p : ℕ) [Fact p.Prime] (j n m : ℕ) : DifferenceFormula n :=
  ⟨ulmLowerFormula p j n m, ulmUpperFormula p j n m⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
