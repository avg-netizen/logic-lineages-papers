module
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument.Proof

theorem exactArgument : Targets.ExactArgument := by
  intro a b
  unfold argument ParametricFinitePairCollapse.ordinal
  rw [mixedArithmetic.1,mixedArithmetic.2]

theorem denotationCalibration : Targets.DenotationCalibration := by
  intro ι G ν s t a b hs ht
  change (ParametricActualCollapse.collapseWith G
    (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0
      (ParametricSourceSuccessor.denoteWith G ν s))
      (ParametricSourceSuccessor.denoteWith G ν t)) : Ordinal)=_
  rw [hs,ht]
  change (ParametricActualCollapse.collapseWith G (argument a b) : Ordinal)=_
  rw [exactArgument]
  rfl
end LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument.Proof
