module
public import LogicLineages.OrdinalComparison.ProfileHeadDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualLimitTailUniqueness : Prop :=
  ∀ (rho sigma : NONote) (n m : Nat), Order.IsSuccLimit rho.1.repr → Order.IsSuccLimit sigma.1.repr →
    rho.1.repr+(n : Ordinal)=sigma.1.repr+(m : Ordinal) → rho=sigma ∧ n=m

end LogicLineages.OrdinalComparison.Targets
