module
public import LogicLineages.ModelsAlgebra.PGroups.RawTrivialExactTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawUpperBounds
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
public import LogicLineages.ModelsAlgebra.PGroups.FiniteScottLower
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
theorem raw_trivial_exact : Targets.rawTrivialExact := by
  intro G _ _
  refine ⟨raw_trivial_pi_one_scott G,?_⟩
  intro q hs
  have hgroup := raw_scott_restriction G (Formula.qf q) hs
  have hp := sigma_qf_padding (1:Ordinal.{0}) one_ne_zero 0 q
  have hScott : GroupScottSentence G (sigmaQF q) := by
    refine ⟨(hp.2 G Fin.elim0).mpr hgroup.1,?_⟩
    intro H _ _ ht
    exact hgroup.2 H ((hp.2 H Fin.elim0).mp ht)
  exact finite_no_sigma_one_scott G (sigmaQF q) hp.1 hScott
end LogicLineages.ModelsAlgebra.PGroups
