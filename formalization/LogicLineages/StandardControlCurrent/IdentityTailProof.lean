module
public import LogicLineages.StandardControlCurrent.IdentityTailTargets
public import LogicLineages.OrdinalComparison.PeakOrbitProof
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent

theorem rootPeakInjectivity : IdentityTailTargets.RootPeakInjectivity :=
  OrdinalComparison.actualRootPeakInjectivity

theorem effectiveFiniteZeros : IdentityTailTargets.EffectiveFiniteZeros :=
  OrdinalComparison.fullActualPositiveFiniteZeros

end LogicLineages.StandardControlCurrent
