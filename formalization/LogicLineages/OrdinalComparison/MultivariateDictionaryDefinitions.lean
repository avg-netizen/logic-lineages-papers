module
public import LogicLineages.OrdinalComparison.MultivariateCollectedDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def multivariateDictionaryKeysAbove (k : Nat) : MultivariateCollectedTags → Prop
  | .nil => True
  | .cons rho A _ rest => k<multivariateCollectedTagKey rho A ∧ multivariateDictionaryKeysAbove k rest

/-- Canonical finite dictionary storage. This is deliberately only storage:
actual ordinal-head domains and recursive open-argument validity are separate. -/
def MultivariateDictionaryOrdered : MultivariateCollectedTags → Prop
  | .nil => True
  | .cons rho A a rest => 0<a ∧
      multivariateDictionaryKeysAbove (multivariateCollectedTagKey rho A) rest ∧
      MultivariateDictionaryOrdered rest

def multivariateDictionaryCoefficient (k : Nat) : MultivariateCollectedTags → Nat
  | .nil => 0
  | .cons rho A a rest => (if k=multivariateCollectedTagKey rho A then a else 0)+
      multivariateDictionaryCoefficient k rest

def MultivariateCollectedRootOrdered : MultivariateCollectedNF → Prop
  | .mk _ _ tags => MultivariateDictionaryOrdered tags

end LogicLineages.OrdinalComparison
