module
public import LogicLineages.StandardControlCurrent.IdentitySignTargets
public import LogicLineages.OrdinalComparison.MultivariateIdentitySourceProof
public import LogicLineages.OrdinalComparison.OneVariableSignSourceProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent

theorem identityNormalForm : IdentitySignTargets.IdentityNormalForm :=
  OrdinalComparison.MultivariateIdentitySource.full_identity

theorem eventualSigns : IdentitySignTargets.EventualSigns :=
  OrdinalComparison.OneVariableSignSource.full

end LogicLineages.StandardControlCurrent
