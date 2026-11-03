module
public import LogicLineages.OrdinalComparison.KernelReachableInputConventionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelReachableInputConvention.Targets

/-- Exactly degree2, retained mass1, original input4. The parameterized
representation avoids evaluating the enormous closed control value. -/
def ExactCommonFirstStep : Prop := initial 4 = Ordinal.omega0 ^ (2 : Ordinal) ∧ FirstData 4

/-- Exactly the differing second transitions at input4 with actual budgets.
No complete-count disagreement or whole numbered theorem refutation. -/
def ExactDifferentSecondSteps : Prop := SecondData 4

end LogicLineages.OrdinalComparison.KernelReachableInputConvention.Targets
