module
public import LogicLineages.OrdinalComparison.MultivariateNormalValidityDefinitions
public import LogicLineages.OrdinalComparison.MultivariatePhiCounterDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Compare the ACTUAL computed literal NF output codes. This final source
algorithm does not redefine normal forms as semantic equivalence classes. -/
noncomputable def encodedMultivariateLiteralIdentity (n m : Nat) : Bool :=
  decide (encodedMultivariateCollectedNormalize n=encodedMultivariateCollectedNormalize m)

end LogicLineages.OrdinalComparison
