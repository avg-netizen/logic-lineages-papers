module
public import LogicLineages.ModelsAlgebra.PGroups.RawUpperBoundsTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawScott
public import LogicLineages.ModelsAlgebra.PGroups.FiniteScott
public import LogicLineages.ModelsAlgebra.PGroups.TrivialScott
public import LogicLineages.ModelsAlgebra.PGroups.BoundedScott
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem raw_finite_difference_scott : Targets.groupRawFiniteDifferenceScott.{u} := by
  intro K _ _
  refine ⟨guardDifference (finiteImageIsomorphismFormula K 1), ?_, ?_⟩
  · exact raw_guard_difference_complexity 1 le_rfl _ (finite_isomorphism_sentence.{u,0,u} K).1
  · exact raw_guard_difference_scott_transfer K _ (finite_difference_scott K)

theorem raw_trivial_pi_one_scott : Targets.groupRawTrivialPiOneScott.{u} := by
  intro G _ _
  refine ⟨guardPi (annihilationFormula 1 0), ?_, ?_⟩
  · exact raw_guard_pi_complexity 1 le_rfl _ trivial_pi_one_scott.{u,0}.1
  · exact raw_guard_scott_transfer G _ (trivial_pi_one_scott.{u,0}.2 G)

theorem raw_bounded_pi_three_scott : Targets.groupRawBoundedPiThreeScott := by
  intro p _ G _ _ N hN
  obtain ⟨entries,hlevel,hscott⟩ := bounded_pi_three_scott p G N hN
  refine ⟨guardPi (boundedUlmTable p N entries), ?_, raw_guard_scott_transfer G _ hscott⟩
  exact raw_guard_pi_complexity 3 (Order.one_le_iff_ne_zero.mpr (by simp)) _ hlevel

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
