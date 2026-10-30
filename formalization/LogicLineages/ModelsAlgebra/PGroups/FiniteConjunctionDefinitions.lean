module

public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunctionDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityDefinitions

@[expose] public section

/-! Literal finite-list normal-form conjunctions. Empty lists use actual
padded true formulas, not an implicit empty-family or rank convention. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

noncomputable def sigmaTwoAll {n : ℕ} : List (Formula n) → Formula n
  | [] => sigmaQF (.neg .falsum)
  | φ :: fs => sigmaTwoConjunction φ (sigmaTwoAll fs)

noncomputable def piTwoAll {n : ℕ} : List (Formula n) → Formula n
  | [] => piQF (.neg .falsum)
  | φ :: fs => piConjunction φ (piTwoAll fs)

noncomputable def differenceTwoAll {n : ℕ} (fs : List (DifferenceFormula n)) : DifferenceFormula n :=
  ⟨sigmaTwoAll (fs.map DifferenceFormula.sigmaPart), piTwoAll (fs.map DifferenceFormula.piPart)⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
