module
public import LogicLineages.ModelsAlgebra.PGroups.RawGroupAxiomsDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunctionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

noncomputable def guardPi (φ : Formula 0) : Formula 0 :=
  piConjunction abelianGroupAxioms φ

noncomputable def guardDifference (d : DifferenceFormula 0) : DifferenceFormula 0 :=
  ⟨d.sigmaPart, guardPi d.piPart⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
