module
public import LogicLineages.ModelsAlgebra.PGroups.ProperRepresentativeTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem proper_representative : Targets.groupProperRepresentative.{u,v} := by
  intro G _ p B x α hx hxnot hproper b hb c β hc
  by_cases hβα : β ≤ α
  · exact transfiniteFiltration_antitone p hβα hb
  · have hab : α + 1 ≤ β := Order.succ_le_of_lt (lt_of_not_ge hβα)
    exact False.elim (hxnot (transfiniteFiltration_antitone p hab (hproper c β hc)))

end LogicLineages.ModelsAlgebra.PGroups
