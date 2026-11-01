module
public import LogicLineages.OrdinalComparison.MultivariateNormalizeCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- A finite coefficient vector with its trailing zero padding omitted. -/
def MultivariateCoefficientCanonical (b : List Nat) : Prop :=
  b=[] ∨ 0<b.getD (b.length-1) 0

/- Storage support is used only with canonical coefficient vectors in the
source validity theorem. Then nonempty stored coefficients mean genuine
nonempty variable support. -/
mutual
  def multivariateCollectedSupport : MultivariateCollectedNF → Bool
    | .mk _ b tags => (b != []) || multivariateCollectedTagsSupport tags
  def multivariateCollectedTagsSupport : MultivariateCollectedTags → Bool
    | .nil => false
    | .cons _ A _ rest => multivariateCollectedSupport A || multivariateCollectedTagsSupport rest
end

mutual
  def MultivariateVectorFields (d : Nat) : MultivariateCollectedNF → Prop
    | .mk _ b tags => b.length≤d ∧ MultivariateCoefficientCanonical b ∧ MultivariateVectorTagsFields d tags
  def MultivariateVectorTagsFields (d : Nat) : MultivariateCollectedTags → Prop
    | .nil => True
    | .cons _ A _ rest => MultivariateVectorFields d A ∧ MultivariateVectorTagsFields d rest
end

/- Literal source normal-form grammar: actual limit heads, finite source
scope, canonical coefficient vectors, nonempty open arguments, positive
coefficients, and strictly ordered unique structural dictionary keys. -/
mutual
  def MultivariateCollectedValid (d : Nat) : MultivariateCollectedNF → Prop
    | .mk _ b tags => b.length≤d ∧ MultivariateCoefficientCanonical b ∧ MultivariateCollectedTagsValid d tags
  def MultivariateCollectedTagsValid (d : Nat) : MultivariateCollectedTags → Prop
    | .nil => True
    | .cons rho A a rest => Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero ∧
        MultivariateCollectedValid d A ∧ multivariateCollectedSupport A=true ∧ 0<a ∧
        multivariateDictionaryKeysAbove (multivariateCollectedTagKey rho A) rest ∧
        MultivariateCollectedTagsValid d rest
end

end LogicLineages.OrdinalComparison
