module
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Explicit structural induction proposition, not an implementation field.
The full strict-mass theorem must prove it for its actual computed threshold. -/
def actualKernelStrictMassAt (theta : Ordinal.{0}) (S : Nat) : Prop :=
  ∀ t a b : Nat, S ≤ t → a < b → b+actualOrdinalNorm theta ≤ t →
    actualSuffixKernel theta b t < actualSuffixKernel theta a t

end LogicLineages.OrdinalComparison
