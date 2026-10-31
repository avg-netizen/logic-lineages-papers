module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
noncomputable def differencePiLift {n:ℕ} (d:DifferenceFormula n) : Formula n :=
  piConjunction (piWrap d.sigmaPart) (piOneNormalize d.piPart)
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
