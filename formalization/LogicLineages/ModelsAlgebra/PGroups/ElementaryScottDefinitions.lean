module

public import LogicLineages.ModelsAlgebra.PGroups.AnnihilationDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunctionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Literal ordinary Pi-two description of infinite exponent-p groups. -/
noncomputable def elementaryAbelianSentence (p : ℕ) : Formula 0 :=
  piTwoAll [annihilationFormula p 0, infiniteMultipleImage 1]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
